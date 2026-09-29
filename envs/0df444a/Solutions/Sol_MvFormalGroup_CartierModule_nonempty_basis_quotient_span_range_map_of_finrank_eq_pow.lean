-- Prove2me | solution 1 for MvFormalGroup.CartierModule.nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6f109a52-de0a-53c3-b49f-dd3e355a10fd

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Theorems.Thm_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
import Theorems.Thm_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_comp_eq_X_pow
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcDegreeFormula

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule

section Iso

variable {k : Type u} [Field k] {d : ℕ}

def linTuple (A : Matrix (Fin d) (Fin d) k) : Fin d → MvPowerSeries (Fin d) k :=
  fun i => ∑ j, A i j • (X j : MvPowerSeries (Fin d) k)

theorem constantCoeff_linTuple (A : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    (linTuple A i).constantCoeff = 0 := by
  simp [linTuple, map_sum, constantCoeff_X]

theorem hasSubst_linTuple (A : Matrix (Fin d) (Fin d) k) : HasSubst (linTuple A) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_linTuple A)

theorem linearPart_linTuple (A : Matrix (Fin d) (Fin d) k) : linearPart (linTuple A) = A := by
  classical
  ext i j
  simp only [linearPart, Matrix.of_apply, linTuple, map_sum, map_smul, coeff_index_single_X,
    smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    simp [Ne.symm hlj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem subst_linTuple {τ : Type*} {b : Fin d → MvPowerSeries τ k} (hb : HasSubst b)
    (A : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst b (linTuple A i) = ∑ j, A i j • b j := by
  simp only [linTuple, ← coe_substAlgHom hb, map_sum, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_substAlgHom hb, subst_X hb]

theorem subst_linTuple_linTuple (A B : Matrix (Fin d) (Fin d) k) (i : Fin d) :
    subst (linTuple B) (linTuple A i) = linTuple (A * B) i := by
  rw [subst_linTuple (hasSubst_linTuple B)]
  simp only [linTuple, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem linTuple_one (i : Fin d) : linTuple (1 : Matrix (Fin d) (Fin d) k) i = X i := by
  classical
  simp only [linTuple, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

variable {Ψ Φ : MvFormalGroup d k}

def blkExt (c : Fin d → MvPowerSeries (Fin d) k) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))

theorem hasSubst_inl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0)
    (s : Fin d ⊕ Fin d) : (blkExt c s).constantCoeff = 0 := by
  rcases s with j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_inl (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  · exact constantCoeff_subst_eq_zero (hasSubst_inr (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)

theorem hasSubst_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0) :
    HasSubst (blkExt c) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blkExt hc)

theorem subst_blkExt_blkExt {c c' : Fin d → MvPowerSeries (Fin d) k}
    (hc : ∀ i, (c i).constantCoeff = 0) (s : Fin d ⊕ Fin d) :
    subst (blkExt c) (blkExt c' s) = blkExt (fun j => subst c (c' j)) s := by
  have hcs := hasSubst_of_constantCoeff_zero hc
  rcases s with j | j
  · show subst (blkExt c) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c' j)) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply (hasSubst_inl (k := k) (d := d)) (hasSubst_blkExt hc),
      subst_comp_subst_apply hcs (hasSubst_inl (k := k) (d := d))]
    congr 1
    funext l
    rw [subst_X (hasSubst_blkExt hc)]
    rfl
  · show subst (blkExt c) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c' j)) =
      subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply (hasSubst_inr (k := k) (d := d)) (hasSubst_blkExt hc),
      subst_comp_subst_apply hcs (hasSubst_inr (k := k) (d := d))]
    congr 1
    funext l
    rw [subst_X (hasSubst_blkExt hc)]
    rfl

theorem blkExt_X' : blkExt (fun i : Fin d => (X i : MvPowerSeries (Fin d) k)) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) := by
  funext s
  rcases s with j | j
  · exact subst_X (hasSubst_inl (k := k) (d := d)) j
  · exact subst_X (hasSubst_inr (k := k) (d := d)) j

def invHom (ψ : Ψ.Hom Φ) (χ : Fin d → MvPowerSeries (Fin d) k)
    (hχ0 : ∀ i, (χ i).constantCoeff = 0)
    (hχψ : ∀ i, subst ψ.toPowerSeries (χ i) = X i)
    (hψχ : ∀ i, subst χ (ψ.toPowerSeries i) = X i) : Φ.Hom Ψ where
  toPowerSeries := χ
  constantCoeff_eq_zero := hχ0
  subst_eq := by
    have hψ0 := ψ.constantCoeff_eq_zero
    have hχs := hasSubst_of_constantCoeff_zero hχ0
    have hψs := ψ.hasSubst_toPowerSeries
    have hEχ := hasSubst_blkExt hχ0
    have hEψ := hasSubst_blkExt hψ0

    set G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun s => subst (blkExt χ) (Ψ.toPowerSeries s)
      with hG
    have hG0 : ∀ s, (G s).constantCoeff = 0 := fun s =>
      constantCoeff_subst_eq_zero hEχ (constantCoeff_blkExt hχ0) (Ψ.constantCoeff_eq_zero s)
    have hGs := hasSubst_of_constantCoeff_zero hG0

    have hstar : ∀ i, subst G (ψ.toPowerSeries i) = Φ.toPowerSeries i := by
      intro i
      have h1 := congrArg (subst (blkExt χ)) (ψ.subst_eq i)
      rw [subst_comp_subst_apply Ψ.hasSubst_toPowerSeries hEχ] at h1
      change subst G (ψ.toPowerSeries i) = _ at h1
      rw [h1]
      change subst (blkExt χ) (subst (blkExt ψ.toPowerSeries) (Φ.toPowerSeries i)) = _
      rw [subst_comp_subst_apply hEψ hEχ]
      have hfam : (fun s => subst (blkExt χ) (blkExt ψ.toPowerSeries s)) =
          fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) := by
        funext s
        rw [subst_blkExt_blkExt hχ0]
        have : (fun j => subst χ (ψ.toPowerSeries j)) = fun j => (X j : MvPowerSeries (Fin d) k) :=
          funext hψχ
        rw [this, blkExt_X']
      rw [hfam]
      exact congrFun subst_self _

    intro i
    show subst Φ.toPowerSeries (χ i) = subst (blkExt χ) (Ψ.toPowerSeries i)
    have h2 : subst G (subst ψ.toPowerSeries (χ i)) = subst Φ.toPowerSeries (χ i) := by
      rw [subst_comp_subst_apply hψs hGs]
      congr 1
      funext s
      exact hstar s
    rw [← h2, hχψ i, subst_X hGs]

theorem exists_inverse (ψ : Ψ.Hom Φ) (hunit : IsUnit (linearPart ψ.toPowerSeries)) :
    ∃ χ : Φ.Hom Ψ, (∀ i, (χ.comp ψ).toPowerSeries i = X i) ∧ (∀ i, (ψ.comp χ).toPowerSeries i = X i) := by
  classical
  have hdet : IsUnit (linearPart ψ.toPowerSeries).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hLiL : (linearPart ψ.toPowerSeries)⁻¹ * linearPart ψ.toPowerSeries = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hLLi : linearPart ψ.toPowerSeries * (linearPart ψ.toPowerSeries)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hψ0 := ψ.constantCoeff_eq_zero
  have hψs := ψ.hasSubst_toPowerSeries
  have hLis := hasSubst_linTuple (linearPart ψ.toPowerSeries)⁻¹

  have hψt0 : ∀ i, (subst ψ.toPowerSeries (linTuple (linearPart ψ.toPowerSeries)⁻¹ i)).constantCoeff = 0 :=
    fun i => constantCoeff_subst_eq_zero hψs hψ0 (constantCoeff_linTuple _ i)
  have hψt1 : linearPart (fun i => subst ψ.toPowerSeries (linTuple (linearPart ψ.toPowerSeries)⁻¹ i)) = 1 := by
    rw [linearPart_subst hψ0, linearPart_linTuple, hLiL]
  obtain ⟨χt, hχt0, hχtψt, hψtχt⟩ :=
    MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one _ hψt0 hψt1
  have hχts := hasSubst_of_constantCoeff_zero hχt0
  have hψts := hasSubst_of_constantCoeff_zero hψt0

  have hχ0 : ∀ i, (subst (linTuple (linearPart ψ.toPowerSeries)⁻¹) (χt i)).constantCoeff = 0 :=
    fun i => constantCoeff_subst_eq_zero hLis (constantCoeff_linTuple _) (hχt0 i)
  have hχs := hasSubst_of_constantCoeff_zero hχ0

  have hχψ : ∀ i, subst ψ.toPowerSeries (subst (linTuple (linearPart ψ.toPowerSeries)⁻¹) (χt i)) = X i := by
    intro i
    rw [subst_comp_subst_apply hLis hψs]
    exact hχtψt i

  have hψeq : ∀ i, ψ.toPowerSeries i =
      subst (fun j => subst ψ.toPowerSeries (linTuple (linearPart ψ.toPowerSeries)⁻¹ j))
        (linTuple (linearPart ψ.toPowerSeries) i) := by
    intro i
    rw [← subst_comp_subst_apply (hasSubst_linTuple _) hψs, subst_linTuple_linTuple, hLLi, linTuple_one,
      subst_X hψs]

  have hψχ : ∀ i, subst (fun l => subst (linTuple (linearPart ψ.toPowerSeries)⁻¹) (χt l))
      (ψ.toPowerSeries i) = X i := by
    intro i
    rw [hψeq i, subst_comp_subst_apply hψts hχs]
    have hfam : (fun j => subst (fun l => subst (linTuple (linearPart ψ.toPowerSeries)⁻¹) (χt l))
        (subst ψ.toPowerSeries (linTuple (linearPart ψ.toPowerSeries)⁻¹ j))) =
        linTuple (linearPart ψ.toPowerSeries)⁻¹ := by
      funext j
      rw [← subst_comp_subst_apply hχts hLis, hψtχt j, subst_X hLis]
    rw [hfam, subst_linTuple_linTuple, hLLi, linTuple_one]
  exact ⟨invHom ψ _ hχ0 hχψ hψχ, fun i => hχψ i, fun i => hψχ i⟩

end Iso

section Main

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}

local notation "𝕎" => WittVector p k
local notation "𝕂" => WittVector p k ⧸ Ideal.span {(p : WittVector p k)}

theorem isMaximal_span_p : (Ideal.span {(p : WittVector p k)}).IsMaximal := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible p)]
  exact IsLocalRing.maximalIdeal.isMaximal _

abbrev pSub (Φ : MvFormalGroup d k) [Φ.IsComm] : Submodule 𝕎 (CartierModule p Φ) :=
  (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule 𝕎 (CartierModule p Φ))

abbrev imgSpan {Ψ Φ : MvFormalGroup d k} [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ) :
    Submodule 𝕂 (CartierModule p Φ ⧸ pSub (p := p) Φ) :=
  Submodule.span 𝕂 (Set.range fun g : CartierModule p Ψ =>
    (Submodule.Quotient.mk (CartierModule.map ψ g) : CartierModule p Φ ⧸ pSub (p := p) Φ))

omit [CharP k p] [PerfectRing k p] in
theorem mem_pSub_iff {Φ : MvFormalGroup d k} [Φ.IsComm] (x : CartierModule p Φ) :
    x ∈ pSub (p := p) Φ ↔ ∃ m : CartierModule p Φ, x = (p : 𝕎) • m := by
  change x ∈ (Ideal.span {(p : 𝕎)} • ⊤ : Submodule 𝕎 (CartierModule p Φ)) ↔ _
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩; exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩; exact ⟨m, Submodule.mem_top, rfl⟩

omit [CharP k p] [PerfectRing k p] in

theorem mk_mem_imgSpan_iff {Ψ Φ : MvFormalGroup d k} [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ)
    (x : CartierModule p Φ) :
    (Submodule.Quotient.mk x : CartierModule p Φ ⧸ pSub (p := p) Φ) ∈ imgSpan (p := p) ψ ↔
      ∃ (g : CartierModule p Ψ) (m : CartierModule p Φ), x = CartierModule.map ψ g + (p : 𝕎) • m := by
  constructor
  · intro hx

    let N : Submodule 𝕎 (CartierModule p Φ) := (mapLinear (p := p) ψ).range ⊔ pSub (p := p) Φ
    let Nbar : Submodule 𝕂 (CartierModule p Φ ⧸ pSub (p := p) Φ) :=
      { carrier := {y | ∃ x ∈ N, Submodule.Quotient.mk x = y}
        add_mem' := by
          rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
          exact ⟨x + x', N.add_mem hx hx', rfl⟩
        zero_mem' := ⟨0, N.zero_mem, rfl⟩
        smul_mem' := by
          rintro c _ ⟨x, hx, rfl⟩
          obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨w • x, N.smul_mem w hx, rfl⟩ }
    have hle : imgSpan (p := p) ψ ≤ Nbar := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨CartierModule.map ψ g, Submodule.mem_sup_left ⟨g, rfl⟩, rfl⟩
    obtain ⟨x', hx'N, hx'x⟩ := hle hx
    have hdiff : x - x' ∈ pSub (p := p) Φ := by
      rw [← Submodule.Quotient.eq]; exact hx'x.symm
    have hxN : x ∈ N := by
      have : x = x' + (x - x') := by abel
      rw [this]
      exact N.add_mem hx'N (Submodule.mem_sup_right hdiff)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxN
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨m, rfl⟩ := (mem_pSub_iff z).mp hz
    exact ⟨g, m, by rw [← hyz]; rfl⟩
  · rintro ⟨g, m, rfl⟩
    rw [Submodule.Quotient.mk_add]
    have h0 : (Submodule.Quotient.mk ((p : 𝕎) • m) : CartierModule p Φ ⧸ pSub (p := p) Φ) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ((mem_pSub_iff _).mpr ⟨m, rfl⟩)
    rw [h0, add_zero]
    exact Submodule.subset_span ⟨g, rfl⟩

omit [CharP k p] [PerfectRing k p] in

theorem finrank_le_one_of_inverse {Ψ Φ : MvFormalGroup d k} (ψ : Ψ.Hom Φ) (χ : Φ.Hom Ψ)
    (hχψ : ∀ i, (χ.comp ψ).toPowerSeries i = X i) :
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) ≤ 1 := by
  set I := Ideal.span (Set.range ψ.toPowerSeries) with hI

  have hmem : ∀ a : MvPowerSeries (Fin d) k, a - C (constantCoeff a) ∈ I := by
    intro a
    set g := a - C (constantCoeff a) with hg
    have hg0 : constantCoeff g = 0 := by simp [hg]

    have hχs := χ.hasSubst_toPowerSeries
    have hψs := ψ.hasSubst_toPowerSeries
    have hh0 : constantCoeff (subst χ.toPowerSeries g) = 0 :=
      constantCoeff_subst_eq_zero hχs χ.constantCoeff_eq_zero hg0
    have hhmem : subst χ.toPowerSeries g ∈ Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k)) := by
      rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]
      exact hh0
    have hmap : Ideal.map (substAlgHom (R := k) hψs)
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k))) = I := by
      rw [Ideal.map_span, hI]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by rw [substAlgHom_apply, subst_X hψs]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨X i, ⟨i, rfl⟩, by rw [substAlgHom_apply, subst_X hψs]⟩
    have hgeq : g = subst ψ.toPowerSeries (subst χ.toPowerSeries g) := by
      rw [subst_comp_subst_apply hχs hψs]
      have : (fun s => subst ψ.toPowerSeries (χ.toPowerSeries s)) = fun s => (X s : MvPowerSeries (Fin d) k) :=
        funext hχψ
      rw [this]
      exact (congrFun subst_self g).symm
    rw [hgeq, ← hmap, ← substAlgHom_apply hψs]
    exact Ideal.mem_map_of_mem _ hhmem

  have hspan : (⊤ : Submodule k (MvPowerSeries (Fin d) k ⧸ I)) ≤
      Submodule.span k {(Ideal.Quotient.mk I 1)} := by
    intro y _
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : Ideal.Quotient.mk I a = constantCoeff a • Ideal.Quotient.mk I 1 := by
      have h1 : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (C (constantCoeff a)) :=
        Ideal.Quotient.eq.mpr (hmem a)
      rw [h1, ← mul_one (C (constantCoeff a)), ← smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk k,
        map_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  calc Module.finrank k (MvPowerSeries (Fin d) k ⧸ I)
      = Module.finrank k (⊤ : Submodule k (MvPowerSeries (Fin d) k ⧸ I)) := (finrank_top k _).symm
    _ ≤ Module.finrank k (Submodule.span k {(Ideal.Quotient.mk I 1)}) :=
        Submodule.finrank_mono hspan
    _ ≤ 1 := by
        refine (finrank_span_le_card _).trans ?_
        simp

omit [CharP k p] [PerfectRing k p] in

theorem finrank_step [(Ideal.span {(p : WittVector p k)}).IsMaximal]
    {Ψ Ψ' Φ : MvFormalGroup d k} [Ψ.IsComm] [Ψ'.IsComm] [Φ.IsComm]
    (ψ : Ψ.Hom Φ) (π : Ψ.Hom Ψ') (ψ' : Ψ'.Hom Φ) (hfac : ψ'.comp π = ψ)
    (hinj : Function.Injective (CartierModule.map (p := p) ψ'))
    (hpψ : ∀ f : CartierModule p Φ, ∃ g : CartierModule p Ψ, CartierModule.map ψ g = (p : 𝕎) • f)
    {r e' : ℕ}
    (bπ : Module.Basis (Fin r) 𝕂 ((CartierModule p Ψ' ⧸ pSub (p := p) Ψ') ⧸ imgSpan (p := p) π))
    (bψ' : Module.Basis (Fin e') 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ')) :
    Nonempty (Module.Basis (Fin (r + e')) 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ)) := by
  letI : Field 𝕂 := Ideal.Quotient.field _

  have hle : imgSpan (p := p) ψ ≤ imgSpan (p := p) ψ' := by
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨CartierModule.map π g, by simp only [← CartierModule.map_comp, hfac]⟩

  let red : (CartierModule p Ψ' ⧸ pSub (p := p) Ψ') →ₗ[𝕂] ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) :=
    { toFun := fun y => Quotient.liftOn' y
        (fun x => (Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x)) :
          (CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ))
        (by
          intro x x' hxx'
          have hd : x - x' ∈ pSub (p := p) Ψ' := (Submodule.quotientRel_def _).mp hxx'
          obtain ⟨m, hm⟩ := (mem_pSub_iff _).mp hd
          show (Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x)) :
              (CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) =
            Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x'))
          have hx : x = x' + (p : 𝕎) • m := by rw [← hm]; abel
          rw [hx, map_add, map_smul_witt, Submodule.Quotient.mk_add]
          have h0 : (Submodule.Quotient.mk ((p : 𝕎) • CartierModule.map ψ' m) : CartierModule p Φ ⧸ pSub (p := p) Φ) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).mpr ((mem_pSub_iff _).mpr ⟨_, rfl⟩)
          rw [h0, add_zero])
      map_add' := by
        intro y y'
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ y'
        rw [← Submodule.Quotient.mk_add]
        show (Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' (x + x'))) :
            (CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) =
          Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x)) +
            Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x'))
        rw [map_add]
        rfl
      map_smul' := by
        intro c y
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
        show (Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' (w • x))) :
            (CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) =
          Ideal.Quotient.mk _ w • Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x))
        rw [map_smul_witt]
        rfl }
  have hred_mk : ∀ x : CartierModule p Ψ',
      red (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.Quotient.mk (CartierModule.map ψ' x)) :=
    fun x => rfl

  have hker : LinearMap.ker red = imgSpan (p := p) π := by
    apply le_antisymm
    · rintro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [LinearMap.mem_ker, hred_mk, Submodule.Quotient.mk_eq_zero, mk_mem_imgSpan_iff] at hy
      obtain ⟨g, m, hgm⟩ := hy
      obtain ⟨g', hg'⟩ := hpψ m

      have hx : x = CartierModule.map π g + CartierModule.map π g' := by
        apply hinj
        rw [map_add, ← CartierModule.map_comp, ← CartierModule.map_comp, hfac, hg', hgm]
      rw [mk_mem_imgSpan_iff]
      exact ⟨g + g', 0, by rw [hx, map_add, smul_zero, add_zero]⟩
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hred_mk, Submodule.Quotient.mk_eq_zero, ← CartierModule.map_comp, hfac]
      exact Submodule.subset_span ⟨g, rfl⟩

  have hrange : LinearMap.range red = (imgSpan (p := p) ψ').map (imgSpan (p := p) ψ).mkQ := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [hred_mk]
      exact ⟨Submodule.Quotient.mk (CartierModule.map ψ' x), Submodule.subset_span ⟨x, rfl⟩, rfl⟩
    · rw [Submodule.map_span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, hred_mk x⟩

  let e1 : ((CartierModule p Ψ' ⧸ pSub (p := p) Ψ') ⧸ imgSpan (p := p) π) ≃ₗ[𝕂]
      ((imgSpan (p := p) ψ').map (imgSpan (p := p) ψ).mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (red.quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ hrange))

  let e2 : (((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) ⧸
      (imgSpan (p := p) ψ').map (imgSpan (p := p) ψ).mkQ) ≃ₗ[𝕂]
      ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ') :=
    Submodule.quotientQuotientEquivQuotient _ _ hle

  set T : Submodule 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) :=
    (imgSpan (p := p) ψ').map (imgSpan (p := p) ψ).mkQ with hT
  haveI hTfin : Module.Finite 𝕂 T := Module.Finite.of_basis (bπ.map e1)
  haveI hQfin : Module.Finite 𝕂 (((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) ⧸ T) :=
    Module.Finite.of_basis (bψ'.map e2.symm)
  haveI : Module.Finite 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) :=
    Module.Finite.of_submodule_quotient T
  have hrank : Module.finrank 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) = r + e' := by
    rw [← Submodule.finrank_quotient_add_finrank T, Module.finrank_eq_card_basis (bψ'.map e2.symm),
      Module.finrank_eq_card_basis (bπ.map e1), Fintype.card_fin, Fintype.card_fin, add_comm]
  exact ⟨Module.finBasisOfFinrankEq _ _ hrank⟩

theorem main (Φ : MvFormalGroup d k) [Φ.IsComm] :
    ∀ (e : ℕ) (Ψ : MvFormalGroup d k) [Ψ.IsComm] (ψ : Ψ.Hom Φ),
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ e →
      (∀ f : CartierModule p Φ, ∃ g : CartierModule p Ψ, CartierModule.map ψ g = (p : 𝕎) • f) →
      Nonempty (Module.Basis (Fin e) 𝕂 ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ)) := by
  haveI := isMaximal_span_p (p := p) (k := k)
  letI : Field 𝕂 := Ideal.Quotient.field _
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    intro Ψ _ ψ hdeg hpψ
    have hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) :=
      Module.finite_of_finrank_pos (by rw [hdeg]; exact pow_pos hp.out.pos e)
    by_cases hunit : IsUnit (linearPart ψ.toPowerSeries)
    ·
      obtain ⟨χ, hχψ, hψχ⟩ := exists_inverse ψ hunit
      have hle1 := finrank_le_one_of_inverse ψ χ hχψ
      have he : e = 0 := by
        have h1 : p ^ e ≤ 1 := hdeg ▸ hle1
        rcases Nat.eq_zero_or_pos e with h | h
        · exact h
        · exact absurd (lt_of_lt_of_le (Nat.one_lt_pow h.ne' hp.out.one_lt) h1) (lt_irrefl _)
      subst he

      have htop : imgSpan (p := p) ψ = ⊤ := by
        rw [eq_top_iff]
        rintro y -
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have hx : x = CartierModule.map ψ (CartierModule.map χ x) := by
          rw [← CartierModule.map_comp]
          have : ψ.comp χ = MvFormalGroup.Hom.id Φ := MvFormalGroup.Hom.ext (funext hψχ)
          rw [this, CartierModule.map_id]
        rw [hx]
        exact Submodule.subset_span ⟨CartierModule.map χ x, rfl⟩
      haveI : Subsingleton ((CartierModule p Φ ⧸ pSub (p := p) Φ) ⧸ imgSpan (p := p) ψ) := by
        rw [htop]
        infer_instance
      exact ⟨Module.Basis.empty _⟩
    ·
      obtain ⟨Ψ', hΨ', π, ρ, ψ', hfac, hcomp, hrank, -, hfinρ, hfinψ', hmul⟩ :=
        MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul p Ψ Φ ψ hfin
      haveI := hΨ'
      set s := (linearPart ψ.toPowerSeries).rank with hs
      set r := d - s with hr

      have hsd : s < d := by
        have hle : s ≤ d := by
          simpa using Matrix.rank_le_card_width (linearPart ψ.toPowerSeries)
        refine lt_of_le_of_ne hle fun hsd' => hunit ?_
        rw [← Matrix.mulVec_surjective_iff_isUnit]
        have hrange : LinearMap.range (linearPart ψ.toPowerSeries).mulVecLin = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [Module.finrank_fin_fun]
          exact hsd'
        exact LinearMap.range_eq_top.mp hrange
      have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hsd)

      have hdvd : Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ∣ p ^ e :=
        ⟨p ^ r, by rw [← hdeg, hmul, mul_comm]⟩
      obtain ⟨e', he'le, he'⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
      have hsum : e = r + e' := by
        have h := hmul
        rw [hdeg, he', ← pow_add] at h
        exact Nat.pow_right_injective hp.out.two_le h
      have he'lt : e' < e := by omega

      have hfacH : ψ'.comp π = ψ := MvFormalGroup.Hom.ext (funext hfac)
      have hinj : Function.Injective (CartierModule.map (p := p) ψ') :=
        map_injective_of_finite_quotient p Ψ' Φ ψ' hfinψ'
      have hpψ' : ∀ f : CartierModule p Φ, ∃ g : CartierModule p Ψ', CartierModule.map ψ' g = (p : 𝕎) • f := by
        intro f
        obtain ⟨g, hg⟩ := hpψ f
        exact ⟨CartierModule.map π g, by rw [← CartierModule.map_comp, hfacH, hg]⟩
      obtain ⟨bψ'⟩ := IH e' he'lt Ψ' ψ' he' hpψ'
      obtain ⟨bπ⟩ := nonempty_basis_quotient_span_range_map_of_comp_eq_X_pow p Ψ Ψ' π ρ hcomp hfinρ
      rw [hrank] at bπ
      obtain ⟨b⟩ := finrank_step ψ π ψ' hfacH hinj hpψ bπ bψ'
      rw [← hsum] at b
      exact ⟨b⟩

end Main

end P2mKcDegreeFormula

open P2mKcDegreeFormula in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ) (e : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ e)
    (hp : ∀ f : MvFormalGroup.CartierModule p Φ, ∃ g : MvFormalGroup.CartierModule p Ψ,
      MvFormalGroup.CartierModule.map ψ g = (p : WittVector p k) • f) :
    Nonempty (Module.Basis (Fin e) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      ((MvFormalGroup.CartierModule p Φ ⧸
          (Ideal.span {(p : WittVector p k)} • ⊤ :
            Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ))) ⧸
        Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
          (Set.range fun g : MvFormalGroup.CartierModule p Ψ =>
            (Submodule.Quotient.mk (MvFormalGroup.CartierModule.map ψ g) :
              MvFormalGroup.CartierModule p Φ ⧸
                (Ideal.span {(p : WittVector p k)} • ⊤ :
                  Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))))) :=
  main Φ e Ψ ψ hdeg hp

end

end S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow (solution)
