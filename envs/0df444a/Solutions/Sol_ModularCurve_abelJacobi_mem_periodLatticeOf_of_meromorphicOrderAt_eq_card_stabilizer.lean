-- Prove2me | solution 1 for ModularCurve.abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9d4c1426-b4af-5e6d-9fc8-18696769f1cd

import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSumOf
import Theorems.Thm_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf
import Theorems.Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
import Theorems.Thm_ModularCurve_abelFibreSumOf_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer

set_option autoImplicit false

open UpperHalfPlane Filter Topology
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "orbifoldIndexOf abelFibreSumOf periodAlongOf periodOf periodLatticeOf periodOf_mem_periodLatticeOf period valueMultiplicity eventually_abelFibreSumOf_sub_mem_periodLatticeOf periodAlongOf_smul_sub_periodAlongOf_eq_periodOf abelFibreSumOf_inv"
namespace AbelNecessityOf
p2m_open "ModularCurve"

section Stabilizer

variable {Γ : Subgroup SL(2, ℤ)}

theorem finite_setOf_smul_eq (τ : ℍ) : {g : SL(2, ℤ) | g • τ = τ}.Finite := by
  have h := ProperlyDiscontinuousSMul.finite_stabilizer' (↥𝒮ℒ) τ
  let φ : SL(2, ℤ) → ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    simpa [φ] using this
  have hset : {g : SL(2, ℤ) | g • τ = τ} = φ ⁻¹' {s : ↥𝒮ℒ | s • τ = τ} := by
    ext g
    rfl
  rw [hset]
  exact h.preimage hφ.injOn

scoped instance finite_stabilizer (Γ' : Subgroup SL(2, ℤ)) (τ : ℍ) :
    Finite (MulAction.stabilizer Γ' τ) := by
  have h := finite_setOf_smul_eq τ
  have : Set.Finite ((MulAction.stabilizer Γ' τ : Set Γ')) := by
    have hsub : (MulAction.stabilizer Γ' τ : Set Γ') = Subtype.val ⁻¹' {g : SL(2, ℤ) | g • τ = τ} := by
      ext γ
      simp [MulAction.mem_stabilizer_iff]
      rfl
    rw [hsub]
    exact h.preimage Subtype.val_injective.injOn
  exact this.to_subtype

theorem neg_one_mem_sup : (-1 : SL(2, ℤ)) ∈ (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem two_le_card_stabilizer (τ : ℍ) :
    2 ≤ Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) := by
  have hnt : Nontrivial (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) := by
    have h1 : (⟨-1, neg_one_mem_sup⟩ : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) ∈
        MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ := by
      rw [MulAction.mem_stabilizer_iff]
      show (-1 : SL(2, ℤ)) • τ = τ
      simp
    refine ⟨⟨1, ⟨_, h1⟩, ?_⟩⟩
    intro h
    have h' := congrArg (fun x : MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ =>
      (((x : (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
    simp at h'
  exact Finite.one_lt_card_iff_nontrivial.mpr hnt

theorem orbifoldIndexOf_pos (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : 0 < ModularCurve.orbifoldIndexOf Γ τ :=
  Nat.div_pos (two_le_card_stabilizer τ) two_pos

end Stabilizer

section Shift

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

local notation "πq" => Quotient.mk (MulAction.orbitRel Γ ℍ)

theorem periodAlong_smul_sub_mem (γ : Γ) (τ : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I (γ • τ) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ ∈ ModularCurve.periodLatticeOf Γ := by
  have h := ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf Γ γ τ
  have h' : ModularCurve.periodAlongOf Γ UpperHalfPlane.I (γ • τ) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ = ModularCurve.periodOf Γ γ := h
  rw [h']
  exact ModularCurve.periodOf_mem_periodLatticeOf Γ γ

theorem periodAlong_out_sub_mem (τ : ℍ) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I ((πq τ).out) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ ∈ ModularCurve.periodLatticeOf Γ := by
  obtain ⟨γ, hγ⟩ := Quotient.mk_out (s := MulAction.orbitRel Γ ℍ) τ
  rw [← hγ]
  exact periodAlong_smul_sub_mem Γ γ τ

theorem sum_mapDomain_sub_sum_mem (c : ℍ →₀ ℤ) :
    ((Finsupp.mapDomain πq c).sum fun ξ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I ξ.out) -
      (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) ∈
        ModularCurve.periodLatticeOf Γ := by
  rw [Finsupp.sum_mapDomain_index
    (h := fun ξ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I (Quotient.out ξ))
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [← smul_sub]
  exact Submodule.smul_mem _ _ (periodAlong_out_sub_mem Γ τ)

end Shift

section Global

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

scoped instance countable_SL2Z : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by unfold Matrix; infer_instance
  exact Subtype.countable

def cuspValues (F : ℍ → ℂ) : Set ℂ :=
  {t | ∃ σ : SL(2, ℤ), Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 t)}

theorem countable_cuspValues (F : ℍ → ℂ) : (cuspValues F).Countable := by
  have : cuspValues F =
      ⋃ σ : SL(2, ℤ), {t | Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 t)} := by
    ext t; simp [cuspValues]
  rw [this]
  refine Set.countable_iUnion fun σ => Set.Subsingleton.countable ?_
  intro t ht s hs
  exact tendsto_nhds_unique ht hs

theorem not_mem_cuspValues_of_ne {F : ℍ → ℂ} {t : ℂ}
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    t ∉ cuspValues F := by
  rintro ⟨σ, hσ⟩
  obtain ⟨L, hL, hL'⟩ := hcusp σ
  exact hL (tendsto_nhds_unique hL' hσ)

theorem abelFibreSum_sub_mem_of_not_mem_cuspValues (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    {t t' : ℂ} (ht : t ∉ cuspValues F) (ht' : t' ∉ cuspValues F) :
    ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t' ∈
      ModularCurve.periodLatticeOf Γ := by
  have hW : IsPreconnected (cuspValues F)ᶜ :=
    ((countable_cuspValues F).isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  set Λ := ModularCurve.periodLatticeOf Γ with hΛ
  let g : ↥((cuspValues F)ᶜ) →
      (Module.Dual ℂ (CuspForm Γ 2)) ⧸ Λ :=
    fun s => Submodule.Quotient.mk (ModularCurve.abelFibreSumOf Γ F s)
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s
    have hs : (s : ℂ) ∉ cuspValues F := s.2
    have hcusp' : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ (s : ℂ) ∧
        Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L) := by
      intro σ
      obtain ⟨L, hL⟩ := hcusp σ
      refine ⟨L, ?_, hL⟩
      rintro rfl
      exact hs ⟨σ, hL⟩
    have hLC := ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf Γ F hF hΓ hnc (s : ℂ)
      hcusp'
    have hpull : ∀ᶠ y : ↥((cuspValues F)ᶜ) in 𝓝 s, ModularCurve.abelFibreSumOf Γ F (y : ℂ) -
        ModularCurve.abelFibreSumOf Γ F (s : ℂ) ∈ Λ :=
      (continuous_subtype_val.continuousAt.tendsto).eventually hLC
    filter_upwards [hpull] with y hy
    exact (Submodule.Quotient.eq Λ).2 hy
  haveI : PreconnectedSpace ↥((cuspValues F)ᶜ) := Subtype.preconnectedSpace hW
  have key := hg.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨t', ht'⟩
  exact (Submodule.Quotient.eq Λ).1 key

end Global

section Degenerate

variable {Γ : Subgroup SL(2, ℤ)}

local notation "πq" => Quotient.mk (MulAction.orbitRel Γ ℍ)

theorem mapDomain_eq_zero_of_order_eq_top (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (cq : Quotient (MulAction.orbitRel Γ ℍ) →₀ ℤ)
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndexOf Γ τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ))
    {t : ℂ} {τ₀ : ℍ}
    (hdeg : meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ₀ : ℂ) = ⊤) : cq = 0 := by

  have ht : t ≠ 0 := by
    rintro rfl
    have := hord τ₀
    simp only [sub_zero] at hdeg
    rw [hdeg] at this
    exact WithTop.top_ne_coe this

  have hall : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤ := by
    intro τ
    by_contra hne
    have hmero : MeromorphicOn (fun z : ℂ => F (ofComplex z) - t) {z : ℂ | 0 < z.im} := by
      intro z hz
      have := (hF ⟨z, hz⟩).sub (MeromorphicAt.const t _)
      exact this
    have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected hpre τ.im_pos τ₀.im_pos hne) hdeg

  have hzero : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = 0 := by
    intro τ
    have hev := meromorphicOrderAt_eq_top_iff.1 (hall τ)
    have hcongr : (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => t := by
      filter_upwards [hev] with z hz
      exact sub_eq_zero.1 hz
    rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_const]
    simp [ht]
  ext ξ
  have h := hord ξ.out
  rw [hzero, Quotient.out_eq] at h
  have h' : ((ModularCurve.orbifoldIndexOf Γ ξ.out : ℤ) * cq ξ : ℤ) = 0 := by
    exact_mod_cast h.symm
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact absurd (by exact_mod_cast h1) (orbifoldIndexOf_pos Γ ξ.out).ne'
  · simpa using h1

end Degenerate

section Compare

variable {Γ : Subgroup SL(2, ℤ)}

local notation "πq" => Quotient.mk (MulAction.orbitRel Γ ℍ)
local notation "Xq" => Quotient (MulAction.orbitRel Γ ℍ)

theorem abelFibreSum_zero_sub_abelFibreSum_inv_zero (F : ℍ → ℂ)
    (cq : Quotient (MulAction.orbitRel Γ ℍ) →₀ ℤ)
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndexOf Γ τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ)) :
    ModularCurve.abelFibreSumOf Γ F 0 - ModularCurve.abelFibreSumOf Γ (fun τ => (F τ)⁻¹) 0 =
      cq.sum fun ξ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I ξ.out := by
  classical
  set e : Xq → ℕ := fun ξ => ModularCurve.orbifoldIndexOf Γ ξ.out with he
  set k : Xq → ℤ := fun ξ => (e ξ : ℤ) * cq ξ with hk
  set P : Xq → Module.Dual ℂ (CuspForm Γ 2) :=
    fun ξ => ModularCurve.periodAlongOf Γ UpperHalfPlane.I ξ.out with hP
  have he_pos : ∀ ξ, 0 < e ξ := fun ξ => orbifoldIndexOf_pos Γ ξ.out

  have hvF : ∀ ξ : Xq, ModularCurve.valueMultiplicity F 0 ξ.out = (k ξ).toNat := by
    intro ξ
    unfold ModularCurve.valueMultiplicity
    simp only [sub_zero]
    rw [hord ξ.out, Quotient.out_eq, WithTop.untop₀_coe]
  have hvG : ∀ ξ : Xq, ModularCurve.valueMultiplicity (fun τ => (F τ)⁻¹) 0 ξ.out = (-k ξ).toNat := by
    intro ξ
    unfold ModularCurve.valueMultiplicity
    simp only [sub_zero]
    rw [show (fun z : ℂ => (F (ofComplex z))⁻¹) = (fun z : ℂ => F (ofComplex z))⁻¹ from rfl,
      meromorphicOrderAt_inv, hord ξ.out, Quotient.out_eq, WithTop.untop₀_neg, WithTop.untop₀_coe]

  set sF : Xq → Module.Dual ℂ (CuspForm Γ 2) :=
    fun ξ => ((ModularCurve.valueMultiplicity F 0 ξ.out : ℂ) /
      (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) • P ξ with hsF
  set sG : Xq → Module.Dual ℂ (CuspForm Γ 2) :=
    fun ξ => ((ModularCurve.valueMultiplicity (fun τ => (F τ)⁻¹) 0 ξ.out : ℂ) /
      (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ)) • P ξ with hsG
  have hdiff : ∀ ξ, sF ξ - sG ξ = ((cq ξ : ℤ) : ℂ) • P ξ := by
    intro ξ
    simp only [hsF, hsG, hvF, hvG]
    rw [← sub_smul, ← sub_div]
    congr 1
    have h1 : ((k ξ).toNat : ℂ) - ((-k ξ).toNat : ℂ) = (k ξ : ℂ) := by
      have := Int.toNat_sub_toNat_neg (k ξ)
      exact_mod_cast this
    rw [h1]
    have hne : (ModularCurve.orbifoldIndexOf Γ ξ.out : ℂ) ≠ 0 := by
      exact_mod_cast (he_pos ξ).ne'
    simp only [hk, he]
    push_cast
    rw [mul_div_cancel_left₀ _ hne]
  have hsuppF : Function.support sF ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp only [hsF, hvF, hk, hc, mul_zero, Int.toNat_zero, Nat.cast_zero, zero_div, zero_smul]
  have hsuppG : Function.support sG ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp only [hsG, hvG, hk, hc, mul_zero, neg_zero, Int.toNat_zero, Nat.cast_zero, zero_div,
      zero_smul]
  have hfinF : (Function.support sF).Finite := cq.support.finite_toSet.subset hsuppF
  have hfinG : (Function.support sG).Finite := cq.support.finite_toSet.subset hsuppG
  have hLHS : ModularCurve.abelFibreSumOf Γ F 0 - ModularCurve.abelFibreSumOf Γ (fun τ => (F τ)⁻¹) 0 =
      ∑ᶠ ξ, (sF ξ - sG ξ) := by
    rw [finsum_sub_distrib hfinF hfinG]
    rfl
  rw [hLHS, finsum_congr hdiff]
  have hsupp : Function.support (fun ξ : Xq => ((cq ξ : ℤ) : ℂ) • P ξ) ⊆ ↑cq.support := by
    intro ξ hξ
    by_contra h0
    have hc : cq ξ = 0 := by simpa [Finsupp.mem_support_iff] using h0
    apply hξ
    simp [hc]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finsupp.sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  exact Int.cast_smul_eq_zsmul ℂ (cq ξ) (P ξ)

end Compare

section Main

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

local notation "πq" => Quotient.mk (MulAction.orbitRel Γ ℍ)

theorem abel_necessity (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 : ℕ) *
        Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel Γ ℍ)) c
          (Quotient.mk (MulAction.orbitRel Γ ℍ) τ) : ℤ) :
        WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf Γ := by
  set Λ := ModularCurve.periodLatticeOf Γ with hΛ
  set cq := Finsupp.mapDomain πq c with hcq
  have hord' : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((ModularCurve.orbifoldIndexOf Γ τ : ℤ) * cq (πq τ) : ℤ) : WithTop ℤ) := hord

  suffices key : (cq.sum fun ξ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I ξ.out) ∈ Λ by
    have hshift := sum_mapDomain_sub_sum_mem Γ c
    have := Λ.sub_mem key hshift
    simpa [hcq] using this
  by_cases hdeg : ∃ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) = ⊤
  ·
    obtain ⟨t, τ₀, hdeg⟩ := hdeg
    have : cq = 0 := mapDomain_eq_zero_of_order_eq_top F hF cq hord' hdeg
    simp [this]
  push Not at hdeg

  set G : ℍ → ℂ := fun τ => (F τ)⁻¹ with hG
  have hGmero : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => G (ofComplex z)) (τ : ℂ) :=
    fun τ => (hF τ).inv
  have hGΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, G (γ • τ) = G τ := by
    intro γ hγ τ
    simp only [hG, hΓ γ hγ τ]
  have hncG : ∀ (s : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => G (ofComplex z) - s) (τ : ℂ) ≠ ⊤ := by
    intro s τ h
    have hev := meromorphicOrderAt_eq_top_iff.1 h
    apply hdeg s⁻¹ τ
    apply meromorphicOrderAt_eq_top_iff.2
    filter_upwards [hev] with z hz
    have hz' : (F (ofComplex z))⁻¹ = s := sub_eq_zero.1 hz
    rw [sub_eq_zero, ← inv_inv (F (ofComplex z)), hz']
  have hcuspF : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L) :=
    fun σ => (hcusp σ).imp fun _ h => h.2
  have hcuspG' : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => G (σ • τ)) atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hL0, hL⟩ := hcusp σ
    exact ⟨L⁻¹, inv_ne_zero hL0, hL.inv₀ hL0⟩
  have hcuspG : ∀ σ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun τ : ℍ => G (σ • τ)) atImInfty (𝓝 L) :=
    fun σ => (hcuspG' σ).imp fun _ h => h.2
  have h0F : (0 : ℂ) ∉ cuspValues F := not_mem_cuspValues_of_ne hcusp
  have h0G : (0 : ℂ) ∉ cuspValues G := not_mem_cuspValues_of_ne hcuspG'

  obtain ⟨t, ht⟩ : (cuspValues F ∪ {0} ∪ Inv.inv '' cuspValues G)ᶜ.Nonempty := by
    have hcount : (cuspValues F ∪ {0} ∪ Inv.inv '' cuspValues G).Countable :=
      ((countable_cuspValues F).union (Set.countable_singleton 0)).union
        ((countable_cuspValues G).image _)
    exact (hcount.dense_compl ℝ).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_image, not_or,
    not_exists, not_and] at ht
  obtain ⟨⟨htF, ht0⟩, htG⟩ := ht
  have htG' : t⁻¹ ∉ cuspValues G := fun h => htG t⁻¹ h (inv_inv t)

  have h1 : ModularCurve.abelFibreSumOf Γ F 0 - ModularCurve.abelFibreSumOf Γ F t ∈ Λ :=
    abelFibreSum_sub_mem_of_not_mem_cuspValues F hF hΓ hdeg hcuspF h0F htF
  have h2 : ModularCurve.abelFibreSumOf Γ G t⁻¹ - ModularCurve.abelFibreSumOf Γ G 0 ∈ Λ :=
    abelFibreSum_sub_mem_of_not_mem_cuspValues G hGmero hGΓ hncG hcuspG htG' h0G
  have h3 : ModularCurve.abelFibreSumOf Γ G t⁻¹ = ModularCurve.abelFibreSumOf Γ F t :=
    ModularCurve.abelFibreSumOf_inv Γ F ht0
  have h4 : ModularCurve.abelFibreSumOf Γ F 0 - ModularCurve.abelFibreSumOf Γ G 0 ∈ Λ := by
    have := Λ.add_mem h1 h2
    rw [h3] at this
    convert this using 1
    abel
  rwa [abelFibreSum_zero_sub_abelFibreSum_inv_zero F cq hord'] at h4

end Main

end ModularCurve.AbelNecessityOf
p2m_reactivate "P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve.AbelNecessityOf"
p2m_reactivate "P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer.ModularCurve"

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (c : UpperHalfPlane →₀ ℤ)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer
            (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 : ℕ) *
        Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane)) c
          (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) τ) : ℤ) : WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf Γ :=
  ModularCurve.AbelNecessityOf.abel_necessity c F hF hΓ hcusp hord

end S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
end P2MW
export P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer (solution)
