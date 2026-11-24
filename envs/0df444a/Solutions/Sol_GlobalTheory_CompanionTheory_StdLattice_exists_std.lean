-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.exists_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:18.929343+00:00
-- url     : https://prove2.me/submissions/6d8e2700-5e6c-4b70-8e67-8ea2e1fc4e47

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_ind_mem_SB
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_psi_dot
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_mem_span_schr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [TopologicalSpace R]
variable [IsTopologicalRing R] [Invertible (2 : R)]
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ S h hM
  classical
  obtain ⟨hrho, -, hc⟩ := hM
  let Γ : AddSubgroup W :=
    AddSubgroup.comap d.e.toLinearMap.toAddMonoidHom ((box O 1 κ).prod (box O u κ))
  have hΓ : ∀ w, w ∈ Γ ↔ (∀ i, (d.e w).1 i ∈ O) ∧ (∀ i, ((u⁻¹ : Rˣ) : R) * (d.e w).2 i ∈ O) := by
    intro w
    show ((∀ i, ((1⁻¹ : Rˣ) : R) * (d.e w).1 i ∈ O) ∧ (∀ i, ((u⁻¹ : Rˣ) : R) * (d.e w).2 i ∈ O)) ↔ _
    simp only [inv_one, Units.val_one, one_mul]
  have hsq : ∀ z : R, ψ (⅟2 * z) ^ 2 = ψ z := by
    intro z
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have hB1 : ∀ γ x, S.c γ x ^ 2 = ψ ((d.e γ).1 ⬝ᵥ (d.e x).2 - (d.e x).1 ⬝ᵥ (d.e γ).2) := by
    intro γ x
    rw [hc, hsq, d.form]
  refine ⟨Γ, fun x => ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))),
    ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx γ hγ
      obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      obtain ⟨hga, hgb⟩ := (hΓ γ).1 hγ
      rw [hB1, AddChar.map_sub_eq_div, psi_dot h hga hxb, psi_dot h hxa hgb, div_one]
    · intro hall
      rw [hΓ]
      constructor
      · intro i
        have key : ∀ z ∈ O, ψ (((u : Rˣ) : R) * (d.e x).1 i * z) = 1 := by
          intro z hz
          have hγ : d.e.symm (0, Pi.single i (((u : Rˣ) : R) * z)) ∈ Γ := by
            rw [hΓ, LinearEquiv.apply_symm_apply]
            refine ⟨fun j => by simp, fun j => ?_⟩
            by_cases hj : j = i <;> simp [Pi.single_apply, hj, hz]
          have h3 := hall _ hγ
          rw [hB1, LinearEquiv.apply_symm_apply] at h3
          simp only [zero_dotProduct, dotProduct_single, zero_sub] at h3
          rw [AddChar.map_neg_eq_inv, inv_eq_one] at h3
          rw [mul_comm ((u : Rˣ) : R) _, mul_assoc]
          exact h3
        have h4 := (h.ann _).1 key
        rwa [← mul_assoc, Units.inv_mul, one_mul] at h4
      · intro i
        apply (h.ann _).1
        intro z hz
        have hγ : d.e.symm (Pi.single i z, 0) ∈ Γ := by
          rw [hΓ, LinearEquiv.apply_symm_apply]
          refine ⟨fun j => ?_, fun j => by simp⟩
          by_cases hj : j = i <;> simp [Pi.single_apply, hj, hz]
        have h3 := hall _ hγ
        rw [hB1, LinearEquiv.apply_symm_apply] at h3
        simp only [single_dotProduct, dotProduct_zero, sub_zero] at h3
        rw [mul_comm]
        exact h3
  · refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
    · obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      have h2 : ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) * ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) = 1 := by
        rw [← pow_two, ← mul_neg, hsq, AddChar.map_neg_eq_inv, psi_dot h hxa hxb, inv_one]
      exact mul_self_eq_one_iff.1 h2
    · obtain ⟨hxa, hxb⟩ := (hΓ x).1 hx
      obtain ⟨hya, hyb⟩ := (hΓ y).1 hy
      show ψ (-(⅟2 * ((d.e (x + y)).1 ⬝ᵥ (d.e (x + y)).2))) =
        ψ (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2))) * ψ (-(⅟2 * ((d.e y).1 ⬝ᵥ (d.e y).2))) * S.c x y
      have h0 : ψ (-(2 * ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2))) = 1 := by
        rw [mul_invOf_self, one_mul, AddChar.map_neg_eq_inv, psi_dot h hxa hyb, inv_one]
      have hX : -(⅟2 * ((d.e x + d.e y).1 ⬝ᵥ (d.e x + d.e y).2)) =
          (-(⅟2 * ((d.e x).1 ⬝ᵥ (d.e x).2)) + -(⅟2 * ((d.e y).1 ⬝ᵥ (d.e y).2)) +
            ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2 - (d.e y).1 ⬝ᵥ (d.e x).2)) +
          -(2 * ⅟2 * ((d.e x).1 ⬝ᵥ (d.e y).2)) := by
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
        ring
      rw [hc, d.form, map_add, hX, AddChar.map_add_eq_mul, h0, mul_one, AddChar.map_add_eq_mul,
        AddChar.map_add_eq_mul]
  · intro γ hγ
    obtain ⟨ha, hb⟩ := (hΓ γ).1 hγ
    apply Subtype.ext
    rw [hrho, Submodule.coe_smul]
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ind, Set.indicator_apply,
      Set.mem_setOf_eq, AddChar.map_neg_eq_inv, inv_inv]
    by_cases hx : ∀ i, x i ∈ O
    · have hxa : ∀ i, (x + (d.e γ).1) i ∈ O := fun i => O.add_mem (hx i) (ha i)
      rw [if_pos hxa, if_pos hx, AddChar.map_add_eq_mul, psi_dot h hx hb, one_mul]
    · have hxa : ¬ ∀ i, (x + (d.e γ).1) i ∈ O := fun h' => hx fun i => by
        simpa using O.sub_mem (h' i) (ha i)
      rw [if_neg hxa, if_neg hx, mul_zero, mul_zero]
  · show Submodule.span ℂ (Set.range fun x => S.rho x ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩) = ⊤
    rw [eq_top_iff]
    rintro g -
    have hg := mem_span_schr h g.2
    have hmap : Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) =
        (Submodule.span ℂ (Set.range fun x => S.rho x ⟨ind O κ, ind_mem_SB h.compact h.isOpen⟩)).map
          (GlobalTheory.WeilM.SB (κ → R)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext f
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨d.e.symm w, ?_⟩
        simp [hrho, GlobalTheory.WeilM.Darboux.rho]
      · rintro ⟨x, rfl⟩
        exact ⟨d.e x, by simp [hrho, GlobalTheory.WeilM.Darboux.rho]⟩
    rw [hmap] at hg
    obtain ⟨y, hy, hyg⟩ := Submodule.mem_map.1 hg
    have hyg' : y = g := Subtype.ext hyg
    rwa [← hyg']
  · intro h0
    have h5 := congrArg (fun g : GlobalTheory.WeilM.SB (κ → R) => (g : (κ → R) → ℂ) 0) h0
    simp [ind, Set.indicator_apply] at h5
end GlobalTheory.CompanionTheory.StdLattice
