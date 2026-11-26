-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.gal_smul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:14:41.397985+00:00
-- url     : https://prove2.me/submissions/94cf97ea-c736-4bd2-8b7d-710d1a9c4b74

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
import Theorems.Thm_GroundTheory_PAdicHodge_gal_smul_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

open GroundTheory.PAdicHodge.ACris in
theorem solution (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) x =
      algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (σ • x) := by
  rw [IsScalarTower.algebraMap_apply (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p)]
  rw [IsScalarTower.algebraMap_apply (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p)]
  change galCris σ
      (algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p)
        (algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) x)) =
    algebraMap (ACrisZero ℂ_[p] p) (ACris ℂ_[p] p)
      (algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (σ • x))
  have h0 : galZero σ (algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) x) =
      algebraMap (AInf ℂ_[p] p) (ACrisZero ℂ_[p] p) (σ • x) := by
    refine Subtype.ext ?_
    change galAway σ (algebraMap (AInf ℂ_[p] p) 𝔸 x) =
      algebraMap (AInf ℂ_[p] p) 𝔸 (σ • x)
    exact galAway_algebraMap σ x
  dsimp [galCris]
  erw [extendEndo_of]
  simp [Algebra.algebraMap_self]
  rw [h0]
  rfl
