-- Prove2me | solution 1 for GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:02.594402+00:00
-- url     : https://prove2.me/submissions/d6598040-2e68-4e37-ab15-d034b0782f41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_transport
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_pi_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ModuleNorm
namespace GlobalTheory.JR.ModuleNorm
theorem _root_.solution (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by
  let eC : (Fin 2 → K) ≃ₜ+ L :=
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }
  let kL : Lˣ := Units.map (algebraMap K L).toMonoidHom k
  have h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k :=
    distribHaarChar_transport eC k kL (fun x => by
      show e (k • x) = kL • e x
      simp only [Units.smul_def]
      rw [map_smul, Algebra.smul_def, smul_eq_mul]
      rfl)
  have h2 := distribHaarChar_pi_two (A := K) k
  let yS : Lˣ := Units.map (starRingEnd L).toMonoidHom y
  let sC : L ≃ₜ+ L :=
    { starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }
  have h3 : distribHaarChar L yS = distribHaarChar L y :=
    distribHaarChar_transport sC y yS (fun x => by
      show star (y • x) = yS • star x
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
      rfl)
  have h4 : kL = y * yS := Units.ext (by simp [kL, yS, h, starRingEnd_apply])
  have hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2 := by
    rw [← h2, ← h1, h4, map_mul, h3, sq]
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq
end GlobalTheory.JR.ModuleNorm
