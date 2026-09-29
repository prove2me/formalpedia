-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7f6ce7dd-3974-5fae-ab93-5c98bfea2d0c

import Mathlib
import Theorems.Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center
import Theorems.Thm_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix MatrixGroups Subgroup MulAction

noncomputable section

namespace OrbifoldSL2

abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))
abbrev Gp : Type := Monoid.CoprodI G23
abbrev PSL : Type := SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ)

def σ : Gp := Monoid.CoprodI.of (M := G23) (i := 0) (Multiplicative.ofAdd 1)
def υ : Gp := Monoid.CoprodI.of (M := G23) (i := 1) (Multiplicative.ofAdd 1)

theorem eq_ofAdd_one_pow' {n : ℕ} [NeZero n] (x : Multiplicative (ZMod n)) :
    x = (Multiplicative.ofAdd (1 : ZMod n)) ^ (Multiplicative.toAdd x).val := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rfl

theorem closure_σ_υ : Subgroup.closure {σ, υ} = (⊤ : Subgroup Gp) := by
  rw [eq_top_iff]
  intro g _
  induction g using Monoid.CoprodI.induction_left with
  | one => exact one_mem _
  | @mul i a x ih =>
    refine mul_mem ?_ (ih (Subgroup.mem_top x))
    have hmem : Monoid.CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1) ∈ Subgroup.closure {σ, υ} := by
      fin_cases i
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    haveI : NeZero (i.val + 2) := ⟨by omega⟩
    rw [eq_ofAdd_one_pow' a, map_pow]
    exact Subgroup.pow_mem _ hmem _

theorem fg_Gp : Group.FG Gp := by
  classical
  exact ⟨⟨{σ, υ}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact closure_σ_υ⟩⟩

theorem range_of_eq_zpowers (i : Fin 2) :
    (Monoid.CoprodI.of (M := G23) (i := i)).range
      = Subgroup.zpowers (Monoid.CoprodI.of (M := G23) (i := i) (Multiplicative.ofAdd 1)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    haveI : NeZero (i.val + 2) := ⟨by omega⟩
    rw [eq_ofAdd_one_pow' x, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  · rw [Subgroup.zpowers_le]
    exact ⟨_, rfl⟩

def e : Gp ≃* PSL := ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose

theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

theorem e_σ : e σ = QuotientGroup.mk ModularGroup.S :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.1

theorem e_υ : e υ = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ModularGroup.exists_mulEquiv_freeProduct_quotient_center.choose_spec.2

def π : SL(2, ℤ) →* Gp := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

theorem π_apply (g : SL(2, ℤ)) : π g = e.symm (QuotientGroup.mk g) := rfl

theorem π_S : π ModularGroup.S = σ := by
  rw [π_apply, ← e_σ, MulEquiv.symm_apply_apply]

theorem π_ST : π (ModularGroup.S * ModularGroup.T) = υ := by
  rw [π_apply, ← e_υ, MulEquiv.symm_apply_apply]

theorem π_surjective : Function.Surjective π :=
  e.symm.surjective.comp (QuotientGroup.mk'_surjective _)

theorem mem_ker_π_iff (z : SL(2, ℤ)) : z ∈ π.ker ↔ z = 1 ∨ z = -1 := by
  rw [MonoidHom.mem_ker, π_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, mem_center_iff_eq]

theorem π_ker_le (Γ : Subgroup SL(2, ℤ)) (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : π.ker ≤ Γ := by
  intro z hz
  rcases (mem_ker_π_iff z).mp hz with rfl | rfl
  · exact one_mem Γ
  · exact hneg

theorem neg_one_mem_zpowers_S : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers ModularGroup.S := by
  have h : ModularGroup.S ^ 2 = -1 := by decide
  rw [← h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2

theorem neg_one_mem_zpowers_ST : (-1 : SL(2, ℤ)) ∈ Subgroup.zpowers (ModularGroup.S * ModularGroup.T) := by
  have h : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by decide
  rw [← h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 3

theorem map_zpowers_S : (Subgroup.zpowers ModularGroup.S).map π = (Monoid.CoprodI.of (M := G23) (i := 0)).range := by
  rw [MonoidHom.map_zpowers, π_S, range_of_eq_zpowers]; rfl

theorem map_zpowers_ST : (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)).map π
    = (Monoid.CoprodI.of (M := G23) (i := 1)).range := by
  rw [MonoidHom.map_zpowers, π_ST, range_of_eq_zpowers]; rfl

section DoubleCoset

variable {M : Type*} [Group M] (A B : Subgroup M)

def dcFlipAux (g : M) : orbitRel.Quotient B (M ⧸ A) :=
  Quotient.mk _ ((g⁻¹ : M) : M ⧸ A)

theorem dcFlipAux_eq (g : M) (a : A) (b : B) :
    dcFlipAux A B ((a : M) * g * (b : M)) = dcFlipAux A B g := by
  apply Quotient.sound
  refine ⟨b⁻¹, ?_⟩
  show ((b⁻¹ : B) : M) • ((g⁻¹ : M) : M ⧸ A) = (((a : M) * g * b)⁻¹ : M)
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
  show (((b : M)⁻¹ * g⁻¹ : M) : M ⧸ A) = (((b : M)⁻¹ * (g⁻¹ * (a : M)⁻¹) : M) : M ⧸ A)
  rw [QuotientGroup.eq]
  have : ((b : M)⁻¹ * g⁻¹)⁻¹ * ((b : M)⁻¹ * (g⁻¹ * (a : M)⁻¹)) = (a : M)⁻¹ := by group
  rw [this]
  exact A.inv_mem a.2

def dcFlip : orbitRel.Quotient A (M ⧸ B) → orbitRel.Quotient B (M ⧸ A) :=
  Quotient.lift
    (Quotient.lift (dcFlipAux A B) (fun g g' (h : QuotientGroup.leftRel B g g') => by
      rw [QuotientGroup.leftRel_apply] at h
      have : g' = (((1 : A) : M) * g * ((⟨g⁻¹ * g', h⟩ : B) : M)) := by simp
      rw [this, dcFlipAux_eq]))
    (fun x y (hxy : x ∈ orbit A y) => by
      obtain ⟨a, rfl⟩ := hxy
      induction y using QuotientGroup.induction_on with | H g =>
      show dcFlipAux A B ((a : M) * g) = dcFlipAux A B g
      have : (a : M) * g = (a : M) * g * ((1 : B) : M) := by simp
      rw [this, dcFlipAux_eq])

theorem dcFlip_mk (g : M) :
    dcFlip A B (Quotient.mk _ (g : M ⧸ B)) = Quotient.mk _ ((g⁻¹ : M) : M ⧸ A) := rfl

theorem dcFlip_dcFlip (x : orbitRel.Quotient A (M ⧸ B)) : dcFlip B A (dcFlip A B x) = x := by
  induction x using Quotient.inductionOn with | h y =>
  induction y using QuotientGroup.induction_on with | H g =>
  rw [dcFlip_mk, dcFlip_mk, inv_inv]

def dcEquiv : orbitRel.Quotient A (M ⧸ B) ≃ orbitRel.Quotient B (M ⧸ A) where
  toFun := dcFlip A B
  invFun := dcFlip B A
  left_inv := dcFlip_dcFlip A B
  right_inv := dcFlip_dcFlip B A

end DoubleCoset

section Main

variable (Γ : Subgroup SL(2, ℤ))

abbrev Hm : Subgroup Gp := Γ.map π

theorem mem_Γ_iff (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (g : SL(2, ℤ)) : g ∈ Γ ↔ π g ∈ Hm Γ := by
  conv_lhs => rw [← Subgroup.comap_map_eq_self (π_ker_le Γ hneg)]
  rfl

theorem index_Hm (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : (Hm Γ).index = Γ.index := Subgroup.index_map_eq _ π_surjective (π_ker_le Γ hneg)

def θ : SL(2, ℤ) ⧸ Γ → Gp ⧸ Hm Γ :=
  Quotient.map' π fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem π h

@[scoped simp] theorem θ_mk (g : SL(2, ℤ)) : θ Γ (g : SL(2, ℤ) ⧸ Γ) = ((π g : Gp) : Gp ⧸ Hm Γ) := rfl

theorem θ_injective (hneg : (-1 : SL(2, ℤ)) ∈ Γ) : Function.Injective (θ Γ) := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a =>
  induction y using QuotientGroup.induction_on with | H b =>
  rw [θ_mk, θ_mk, QuotientGroup.eq, ← map_inv, ← map_mul, ← mem_Γ_iff Γ hneg] at h
  exact QuotientGroup.eq.mpr h

theorem θ_surjective : Function.Surjective (θ Γ) := by
  intro y
  induction y using QuotientGroup.induction_on with | H k =>
  obtain ⟨g, rfl⟩ := π_surjective k
  exact ⟨(g : SL(2, ℤ) ⧸ Γ), rfl⟩

theorem θ_smul (g : SL(2, ℤ)) (x : SL(2, ℤ) ⧸ Γ) : θ Γ (g • x) = π g • θ Γ x := by
  induction x using QuotientGroup.induction_on with | H a =>
  show θ Γ ((g * a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ) = ((π g * π a : Gp) : Gp ⧸ Hm Γ)
  rw [θ_mk, map_mul]

def orbitEquiv (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (A : Subgroup SL(2, ℤ)) :
    orbitRel.Quotient A (SL(2, ℤ) ⧸ Γ) ≃ orbitRel.Quotient (A.map π) (Gp ⧸ Hm Γ) :=
  Quotient.congr (Equiv.ofBijective (θ Γ) ⟨θ_injective Γ hneg, θ_surjective Γ⟩) (fun x y => by
    show x ∈ orbit A y ↔ θ Γ x ∈ orbit (A.map π) (θ Γ y)
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨⟨π a, Subgroup.mem_map_of_mem π a.2⟩, ?_⟩
      show π (a : SL(2, ℤ)) • θ Γ y = θ Γ ((a : SL(2, ℤ)) • y)
      rw [θ_smul]
    · rintro ⟨⟨_, a, ha, rfl⟩, h⟩
      refine ⟨⟨a, ha⟩, θ_injective Γ hneg ?_⟩
      show θ Γ (a • y) = θ Γ x
      rw [θ_smul]
      exact h)

variable (K : Type) [Field K]

abbrev f : Γ →* Hm Γ := π.subgroupMap Γ

theorem f_surjective : Function.Surjective (f Γ) := π.subgroupMap_surjective Γ

theorem apply_eq_zero_of_mem_ker (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) {x : Γ} (hx : x ∈ (f Γ).ker) :
    φ (Additive.ofMul x) = 0 := by
  have hx' : (x : SL(2, ℤ)) ∈ π.ker := by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  rcases (mem_ker_π_iff _).mp hx' with h1 | h1
  · have : x = 1 := Subtype.ext h1
    rw [this, ofMul_one, map_zero]
  · have hsq : x * x = 1 := Subtype.ext (by rw [Subgroup.coe_mul, h1]; simp)
    have h3 : (2 : K) * φ (Additive.ofMul x) = 0 := by
      rw [two_mul, ← map_add, ← ofMul_mul, hsq, ofMul_one, map_zero]
    exact (mul_eq_zero.mp h3).resolve_left h2

theorem apply_eq_of_f_eq (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) {γ γ' : Γ} (h : f Γ γ = f Γ γ') :
    φ (Additive.ofMul γ) = φ (Additive.ofMul γ') := by
  have hker : γ⁻¹ * γ' ∈ (f Γ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h0 := apply_eq_zero_of_mem_ker Γ K h2 φ hker
  rw [ofMul_mul, ofMul_inv, map_add, map_neg, neg_add_eq_zero] at h0
  exact h0

def descFun (φ : Additive Γ →+ K) (x : Additive (Hm Γ)) : K :=
  φ (Additive.ofMul (Classical.choose (f_surjective Γ (Additive.toMul x))))

theorem descFun_apply (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) (γ : Γ) :
    descFun Γ K φ (Additive.ofMul (f Γ γ)) = φ (Additive.ofMul γ) :=
  apply_eq_of_f_eq Γ K h2 φ (Classical.choose_spec (f_surjective Γ (Additive.toMul (Additive.ofMul (f Γ γ)))))

def desc (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) : Additive (Hm Γ) →+ K where
  toFun := descFun Γ K φ
  map_zero' := by
    have h := descFun_apply Γ K h2 φ 1
    rw [map_one, ofMul_one, ofMul_one, map_zero] at h
    exact h
  map_add' x y := by
    obtain ⟨γ, hγ⟩ := f_surjective Γ (Additive.toMul x)
    obtain ⟨δ, hδ⟩ := f_surjective Γ (Additive.toMul y)
    have hx : x = Additive.ofMul (f Γ γ) := by rw [hγ]; rfl
    have hy : y = Additive.ofMul (f Γ δ) := by rw [hδ]; rfl
    rw [hx, hy, ← ofMul_mul, ← map_mul, descFun_apply Γ K h2, descFun_apply Γ K h2,
      descFun_apply Γ K h2, ofMul_mul, map_add]

theorem desc_apply (h2 : (2 : K) ≠ 0) (φ : Additive Γ →+ K) (γ : Γ) :
    desc Γ K h2 φ (Additive.ofMul (f Γ γ)) = φ (Additive.ofMul γ) :=
  descFun_apply Γ K h2 φ γ

def descL (h2 : (2 : K) ≠ 0) : (Additive Γ →+ K) →ₗ[K] (Additive (Hm Γ) →+ K) where
  toFun := desc Γ K h2
  map_add' φ ψ := by
    ext x
    obtain ⟨γ, rfl⟩ := f_surjective Γ (Additive.toMul x)
    show desc Γ K h2 (φ + ψ) (Additive.ofMul (f Γ γ)) = desc Γ K h2 φ (Additive.ofMul (f Γ γ))
      + desc Γ K h2 ψ (Additive.ofMul (f Γ γ))
    rw [desc_apply, desc_apply, desc_apply]; rfl
  map_smul' c φ := by
    ext x
    obtain ⟨γ, rfl⟩ := f_surjective Γ (Additive.toMul x)
    show desc Γ K h2 (c • φ) (Additive.ofMul (f Γ γ)) = c • desc Γ K h2 φ (Additive.ofMul (f Γ γ))
    rw [desc_apply, desc_apply]; rfl

theorem moduleFinite_hom [(Hm Γ).FiniteIndex] : Module.Finite K (Additive (Hm Γ) →+ K) := by
  classical
  haveI : Group.FG Gp := fg_Gp
  haveI hΓ : Group.FG (Hm Γ) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨s, hs⟩ := hΓ.out
  let ev : (Additive (Hm Γ) →+ K) →ₗ[K] (s → K) :=
    { toFun := fun φ i => φ (Additive.ofMul (i : Hm Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective ev ?_
  intro φ ψ h
  have key : ∀ γ : Hm Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (s : Set (Hm Γ)) := by rw [hs]; exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact congrFun h ⟨x, hx⟩
    | one => rw [ofMul_one, map_zero, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, map_add, hx, hy]
    | inv x _ hx => rw [ofMul_inv, map_neg, map_neg, hx]
  exact AddMonoidHom.ext fun x => key (Additive.toMul x)

theorem descL_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (descL Γ K h2) := by
  intro φ ψ h
  apply AddMonoidHom.ext
  intro x
  have := congrArg (fun χ : Additive (Hm Γ) →+ K => χ (Additive.ofMul (f Γ (Additive.toMul x)))) h
  change desc Γ K h2 φ (Additive.ofMul (f Γ (Additive.toMul x)))
    = desc Γ K h2 ψ (Additive.ofMul (f Γ (Additive.toMul x))) at this
  rwa [desc_apply, desc_apply] at this

end Main

end OrbifoldSL2
p2m_reactivate "P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.OrbifoldSL2"

open OrbifoldSL2 in
theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Module.finrank K (Additive Γ →+ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Γ.index + 1 := by
  haveI : (Hm Γ).FiniteIndex := ⟨by rw [index_Hm Γ hneg]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  have hK : ∀ i : Fin 2, (Nat.card (G23 i) : K) ≠ 0 := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    fin_cases i
    · exact h2
    · exact h3
  have hmain : Module.finrank K (Additive (Hm Γ) →+ K)
      + Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 0)).range))
      + Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 1)).range))
      ≤ Γ.index + 1 := by
    have h := Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
      (G := G23) (Hm Γ) K hK
    rw [index_Hm Γ hneg] at h
    exact h
  haveI := moduleFinite_hom Γ K
  have hhom : Module.finrank K (Additive Γ →+ K) ≤ Module.finrank K (Additive (Hm Γ) →+ K) :=
    LinearMap.finrank_le_finrank_of_injective (descL_injective Γ K h2)
  have hS : Nat.card (orbitRel.Quotient (Subgroup.zpowers ModularGroup.S) (SL(2, ℤ) ⧸ Γ))
      = Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 0)).range)) := by
    rw [Nat.card_congr (orbitEquiv Γ hneg (Subgroup.zpowers ModularGroup.S)), map_zpowers_S,
      Nat.card_congr (dcEquiv _ _)]
  have hST : Nat.card (orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) (SL(2, ℤ) ⧸ Γ))
      = Nat.card (orbitRel.Quotient (Hm Γ) (Gp ⧸ (Monoid.CoprodI.of (M := G23) (i := 1)).range)) := by
    rw [Nat.card_congr (orbitEquiv Γ hneg (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))),
      map_zpowers_ST, Nat.card_congr (dcEquiv _ _)]
  rw [hS, hST]
  omega

#print axioms solution

end
end S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
end P2MW
export P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one (solution)
