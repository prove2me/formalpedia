-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.geometricPart_realpart_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:32:08.174903+00:00
-- url     : https://prove2.me/submissions/19ab42d7-c9c1-4abd-92cd-d782b40d6e63

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
theorem kt_geom (Z : A) (hZ : ‖Z‖ < 1) :
    0 ≤ 1 + (∑' n : ℕ, Z ^ (n+1)) + star (∑' n : ℕ, Z ^ (n+1)) := by
  set G := ∑' n : ℕ, Z ^ n with hGdef
  have hsum : Summable (fun n : ℕ => Z ^ n) := summable_geometric_of_norm_lt_one hZ
  have hS : (∑' n : ℕ, Z ^ (n+1)) = G - 1 := by
    rw [hGdef, hsum.tsum_eq_zero_add]; simp
  have hR : (1 - Z) * G = 1 := mul_neg_geom_series Z hZ
  have hZG : Z * G = G - 1 := by
    rw [sub_mul, one_mul] at hR
    rw [← hR]; abel
  have hGZ : star G * star Z = star G - 1 := by
    have := congrArg star hZG; rwa [star_mul, star_sub, star_one] at this
  have key : 1 + (G - 1) + star (G - 1) = star G * (1 - star Z * Z) * G := by
    have : star G * (1 - star Z * Z) * G = star G * G - (star G * star Z) * (Z * G) := by noncomm_ring
    rw [this, hGZ, hZG, star_sub, star_one]; noncomm_ring
  rw [hS, key]
  apply star_left_conjugate_nonneg
  have h1 := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := Z)
  have h2 : algebraMap ℝ A (‖Z‖ ^ 2) ≤ 1 := by
    rw [← map_one (algebraMap ℝ A)]
    apply algebraMap_mono
    have := norm_nonneg Z
    nlinarith
  exact sub_nonneg.2 (h1.trans h2)

theorem solution (Z : A) (hZ : ‖Z‖ < 1) :
    0 ≤ 1 + (∑' n : ℕ, Z ^ (n+1)) + star (∑' n : ℕ, Z ^ (n+1)) := kt_geom Z hZ
