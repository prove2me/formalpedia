-- Prove2me | solution 1 for GlobalTheory.JR.PartialInv.selfDual_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:59.409805+00:00
-- url     : https://prove2.me/submissions/a9de4b2a-f568-43ad-ab62-d0624003b01c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
import Theorems.Thm_GlobalTheory_JR_PartialInv_mem_intLat
import Theorems.Thm_GlobalTheory_T_selfDual_iff_lattice_volume_and_plancherel_alt
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv
namespace GlobalTheory.JR.PartialInv
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hcond := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.1
  have hsymm : LinearMap.BilinForm.IsSymm (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) :=
    ⟨fun x y => by simp [dotProduct_comm]⟩
  have hnd : LinearMap.BilinForm.Nondegenerate (dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) := by
    constructor
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
    · intro x hx
      ext i
      simpa using hx (Pi.single i 1)
  have hopen : IsOpen (intLat F r : Set (Fin r → F)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hcpt : IsCompact (intLat F r : Set (Fin r → F)) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hvol : (Measure.pi fun _ : Fin r => M.μF) (intLat F r : Set (Fin r → F)) = 1 := by
    change (Measure.pi fun _ : Fin r => M.μF) (Set.univ.pi fun _ => Metric.closedBall (0 : F) 1) = 1
    rw [Measure.pi_pi]
    simp [M.volF]
  have hdual : {y : Fin r → F | ∀ x ∈ intLat F r,
      ψ ((dotProductBilin F F : LinearMap.BilinForm F (Fin r → F)) x y) = 1} = (intLat F r : Set (Fin r → F)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_intLat, dotProductBilin_apply_apply]
    constructor
    · intro h i
      refine (hcond (y i)).1 fun e he => ?_
      have := h (Pi.single i e) (fun j => by
        by_cases hj : j = i
        · subst hj; simpa using he
        · simp [hj])
      simpa using this
    · intro h x hx
      refine hψ.1 _ ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (h i)
  have key := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → F) (dotProductBilin F F) hsymm hnd
    (Measure.pi fun _ : Fin r => M.μF) inferInstance).1 (intLat F r) hopen hcpt).1
  rw [hdual, hvol] at key
  exact key.2 (mul_one 1)
end GlobalTheory.JR.PartialInv
