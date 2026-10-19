-- Prove2me | solution 2 for OAI.CirculantHadamard.binary_signed_product_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:20:26.774297+00:00
-- url     : https://prove2.me/submissions/7930ba12-c4f8-4438-9862-cf6d01286b27

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryResidue.lean:L116-L135
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.binary_signed_product_residue_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryResidue ----
namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

section Domain

variable [IsDomain O]

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

omit charTwo in
/-- A signed product of units with residue one again has residue one.
The powers are formed in the unit group, including for negative exponents. -/
theorem binary_signed_product_residue_one [CharP k 2] {ι : Type uIota}
    (φ : O →+* k) (s : Finset ι) (u : ι → Oˣ) (ε : ι → ℤ)
    (hu : ∀ j ∈ s, φ (u j : O) = 1) :
    φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 := by
  let f : Oˣ →* kˣ := Units.map φ.toMonoidHom
  have hf (j : ι) (hj : j ∈ s) : f (u j) = 1 := by
    apply Units.ext
    change φ (u j : O) = 1
    exact hu j hj
  have hp : f (∏ j ∈ s, (u j) ^ (ε j)) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro j hj
    rw [map_zpow, hf j hj, one_zpow]
  have hval := congrArg (fun z : kˣ => (z : k)) hp
  change φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 at hval
  exact hval

variable [IsDomain O]

end Residue

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uO,uk,uIota} : type_of% @_root_.OAI.CirculantHadamard.binary_signed_product_residue_one.{uO,uk,uIota} := @_root_.OAI.CirculantHadamard.binary_signed_product_residue_one.{uO,uk,uIota}
