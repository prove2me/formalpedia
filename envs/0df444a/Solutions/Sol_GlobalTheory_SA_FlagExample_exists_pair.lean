-- Prove2me | solution 1 for GlobalTheory.SA.FlagExample.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:10.094853+00:00
-- url     : https://prove2.me/submissions/212b3001-4d68-417c-888a-6ae1b953a2a5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_isUnimod_ofHSpace
import Theorems.Thm_GlobalTheory_SA_FlagExample_fl_z_mem
import Theorems.Thm_GlobalTheory_SA_FlagExample_isCong_fl
import Theorems.Thm_GlobalTheory_SA_FlagExample_gval_fl
import Theorems.Thm_GlobalTheory_SA_FlagExample_isTransv_fl
import Theorems.Thm_GlobalTheory_SA_FlagExample_isPairMap_flip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
open GlobalTheory.SA.FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
variable {m s : ℤ} (h1 : m * m = m) (h2 : s * s = m)
namespace GlobalTheory.SA.FlagExample
theorem _root_.solution : ∃ (F F' F'' : FlagD (ofHSpace (wittSpace E 2 1)) 1)
    (β : (wittSpace E 2 1).V ≃ₗ[E] (wittSpace E 2 1).V),
    IsUnimod (ofHSpace (wittSpace E 2 1)) (wittSpace E 2 1).L0 ∧
    F.z ∈ (wittSpace E 2 1).L0 ∧ F'.z ∈ (wittSpace E 2 1).L0 ∧ F''.z ∈ (wittSpace E 2 1).L0 ∧
    F.T = 1 ∧ F'.T = 1 ∧ F''.T = 1 ∧
    IsCong F F' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧ IsCong F F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) ∧
    Gval F F' ≠ 0 ∧ Gval F F'' ≠ 0 ∧ IsTransv F F' ∧ IsTransv F F'' ∧ F'.X ≠ F''.X ∧
    IsPairMap F F' F'' (wittSpace E 2 1).L0 ((2 : ℕ) : 𝓞 E) β :=
  ⟨flZero E, flPos E, flNeg E, flip E,
    (isUnimod_ofHSpace _ _).2 ⟨(wittSpace E 2 1).standardTuple_isLattice, (wittSpace E 2 1).baseLattice_isUnimodular⟩,
    fl_z_mem E _ _, fl_z_mem E _ _, fl_z_mem E _ _, rfl, rfl, rfl, isCong_fl E _ _, isCong_fl E _ _,
    by rw [gval_fl]; norm_num, by rw [gval_fl]; norm_num, isTransv_fl E _, isTransv_fl E _, X_ne E,
    isPairMap_flip E⟩
end GlobalTheory.SA.FlagExample
