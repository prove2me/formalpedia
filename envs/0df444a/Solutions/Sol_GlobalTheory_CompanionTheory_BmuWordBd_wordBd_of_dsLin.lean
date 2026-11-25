-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuWordBd.wordBd_of_dsLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:28.418657+00:00
-- url     : https://prove2.me/submissions/d95aa323-0557-46e0-9fde-8810942113bf

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordLengthBoundOfLinear
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuWordBd_exists_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuWordBd_dsW_sum
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
namespace GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private theorem ex_mem_UH_of_lie {n : ℕ} {Hm X : Mat n} (hsq : Hm * Hm = 1) (hX : Lie Hm X) (t : ℝ) :
    ex X t ∈ Formalism.QuantumDeterminants.UH Hm := by
  have hinv : Hm⁻¹ = Hm := Matrix.inv_eq_right_inv hsq
  have hU : IsUnit Hm := ⟨⟨Hm, Hm, hsq, hsq⟩, rfl⟩
  have h1 : Xᴴ * Hm = -(Hm * X) := eq_neg_of_add_eq_zero_left hX
  have hXH : Xᴴ = Hm * (-X) * Hm := by
    calc Xᴴ = Xᴴ * Hm * Hm := by rw [mul_assoc, hsq, mul_one]
      _ = Hm * (-X) * Hm := by rw [h1, Matrix.mul_neg]
  have hconj : ((t : ℂ) • X)ᴴ = Hm * (-((t : ℂ) • X)) * Hm⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXH, hinv]
    simp [Matrix.mul_smul, Matrix.smul_mul, Complex.conj_ofReal]
  show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Hm * NormedSpace.exp ((t : ℂ) • X) = Hm
  rw [← Matrix.exp_conjTranspose, hconj, Matrix.exp_conj _ _ hU, hinv, mul_assoc (Hm * _) Hm Hm, hsq,
    mul_one, mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl ((t : ℂ) • X))),
    neg_add_cancel, NormedSpace.exp_zero, mul_one]
private theorem dsW_append' {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (P W : List (Mat n)) (v : H) :
    dsW σ (P ++ W) v = dsW σ P (dsW σ W v) := by
  show List.foldr (ds σ) v (P ++ W) = List.foldr (ds σ) (List.foldr (ds σ) v W) P
  exact List.foldr_append
end GlobalTheory.CompanionTheory.BmuWordBd
end
end

set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuWordBd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuWordBd
theorem _root_.solution : DsLin → WordBd := by
  intro hD
  unfold WordBd
  intro n Hm H _ _ _ σ hU w hw m
  have hrep : RepOn (Formalism.QuantumDeterminants.UH Hm) σ := hU.rep
  have hsq : Hm * Hm = 1 := hU.sq
  have hlie : ∀ W : List (Mat n), LieWd Hm W → LieW (Formalism.QuantumDeterminants.UH Hm) W :=
    fun W hW X hX t => ex_mem_UH_of_lie hsq (hW X hX) t
  obtain ⟨N, b, κ, hκ, hb, hc⟩ := exists_basis Hm
  have hexp : ∀ v, IsSm (Formalism.QuantumDeterminants.UH Hm) σ v → ∀ X, Lie Hm X →
      ∃ c : Fin N → ℝ, (∀ i, |c i| ≤ κ * ‖X‖) ∧ ds σ X v = ∑ i, (c i : ℂ) • ds σ (b i) v := by
    intro v hv X hX
    obtain ⟨Λ, hΛ⟩ := hD n Hm H σ hU v hv
    obtain ⟨c, hXc, hcb⟩ := hc X hX
    refine ⟨c, hcb, ?_⟩
    rw [hΛ X hX, hXc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hΛ (b i) (hb i), Complex.coe_smul]
  have hlb : ∀ i, LieWd Hm [b i] := by
    intro i Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact hb i
  have key : ∀ k : ℕ, ∀ P : List (Mat n), LieWd Hm P → ∃ C : ℝ, 0 ≤ C ∧
      ∀ W : List (Mat n), LieWd Hm W → W.length ≤ k →
        ‖dsW σ (P ++ W) w‖ ≤ C * (W.map (fun X => ‖X‖)).prod := by
    intro k
    induction k with
    | zero =>
      intro P _
      refine ⟨‖dsW σ P w‖, norm_nonneg _, fun W _ hW => ?_⟩
      have hW0 : W = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hW)
      subst hW0
      simp
    | succ k ih =>
      intro P hP
      have hPb : ∀ i, LieWd Hm (P ++ [b i]) := by
        intro i Y hY
        rcases List.mem_append.1 hY with h | h
        · exact hP Y h
        · exact hlb i Y h
      choose C hC0 hC using fun i : Fin N => ih (P ++ [b i]) (hPb i)
      refine ⟨max ‖dsW σ P w‖ (κ * ∑ i, C i), le_max_of_le_left (norm_nonneg _), ?_⟩
      intro W hW hlen
      cases W with
      | nil =>
        simp only [List.append_nil, List.map_nil, List.prod_nil, mul_one]
        exact le_max_left _ _
      | cons X W' =>
        have hX : Lie Hm X := hW X List.mem_cons_self
        have hW' : LieWd Hm W' := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
        have hlen' : W'.length ≤ k := by simpa using hlen
        have hv : IsSm (Formalism.QuantumDeterminants.UH Hm) σ (dsW σ W' w) := hw.dsW hrep (hlie W' hW')
        obtain ⟨c, hcb, hds⟩ := hexp _ hv X hX
        have hsm : ∀ i, IsSm (Formalism.QuantumDeterminants.UH Hm) σ (ds σ (b i) (dsW σ W' w)) :=
          fun i => hv.dsW hrep (hlie [b i] (hlb i))
        have heq : dsW σ (P ++ X :: W') w = ∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w := by
          rw [dsW_append', dsW_cons, hds,
            (dsW_sum hrep Finset.univ _ (fun i => (hsm i).smul (c i : ℂ)) (hlie P hP)).2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dsW_smul hrep (hsm i) _ (hlie P hP), dsW_append', dsW_append']
          rfl
        have hprod : 0 ≤ (W'.map (fun X => ‖X‖)).prod :=
          List.prod_nonneg (fun a ha => by
            obtain ⟨Y, _, rfl⟩ := List.mem_map.1 ha
            exact norm_nonneg _)
        simp only [List.map_cons, List.prod_cons]
        rw [heq]
        calc ‖∑ i, (c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖
            ≤ ∑ i, ‖(c i : ℂ) • dsW σ ((P ++ [b i]) ++ W') w‖ := norm_sum_le _ _
          _ ≤ ∑ i, (κ * ‖X‖) * (C i * (W'.map (fun X => ‖X‖)).prod) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
              exact mul_le_mul (hcb i) (hC i W' hW' hlen') (norm_nonneg _)
                (mul_nonneg hκ (norm_nonneg _))
          _ = (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) := by
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ ≤ max ‖dsW σ P w‖ (κ * ∑ i, C i) * (‖X‖ * (W'.map (fun X => ‖X‖)).prod) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) hprod)
  obtain ⟨C, hC0, hC⟩ := key m [] (fun X hX => absurd hX List.not_mem_nil)
  exact ⟨C, hC0, fun W hW hlen => by simpa using hC W hW hlen⟩
end GlobalTheory.CompanionTheory.BmuWordBd
