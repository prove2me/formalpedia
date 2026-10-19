-- Prove2me | solution 2 for OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:17:51.572624+00:00
-- url     : https://prove2.me/submissions/d8755b24-1d71-4c20-9744-57fc63265039

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/FirstOrderResidue.lean:L105-L147
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.FirstOrderResidue ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uO uK uIota

/-!
# First-order residues of principal units

For a nonzero element `t` of a domain, a unit of the form `1 + t * a` has a
unique coefficient `a`. A ring homomorphism killing `t` sends the coefficient
of a product to the sum of the coefficients. This constructs the actual
first-order homomorphism without identifying any quotient rings.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

section Domain

variable [IsDomain O]

variable {K : Type uK} [Field K]

theorem actualFirstOrder_apply_of_eq (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) (u : principalUnits t) {a : O}
    (ha : ((u : Oˣ) : O) = 1 + t * a) :
    (actualFirstOrder φ t ht hφt u).toAdd = φ a := by
  change φ (principalUnitCoeff t u) = φ a
  rw [principalUnitCoeff_eq t ht u ha]

/-- An exact signed product identity among principal units gives a vanishing
sum of their first-order residues. Representations are required only on `s`. -/
theorem first_order_sum_eq_zero_of_prod_eq_one {ι : Type uIota}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by
  classical
  let v : ι → principalUnits t := fun i =>
    if hi : i ∈ s then ⟨u i, ⟨L i, hrep i hi⟩⟩ else 1
  have hv (i : ι) (hi : i ∈ s) : (v i : Oˣ) = u i := by
    simp only [v, dite_eq_left hi]
  have hp : (∏ i ∈ s, (v i) ^ (ε i)) = 1 := by
    apply Subtype.ext
    change (principalUnits t).subtype (∏ i ∈ s, (v i) ^ (ε i)) =
      (principalUnits t).subtype 1
    rw [map_prod, map_one]
    calc
      (∏ i ∈ s, (principalUnits t).subtype ((v i) ^ (ε i))) =
          ∏ i ∈ s, (u i) ^ (ε i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [map_zpow]
        change (v i : Oˣ) ^ (ε i) = (u i) ^ (ε i)
        rw [hv i hi]
      _ = 1 := hprod
  have hmap := congrArg
    (fun z : principalUnits t => (actualFirstOrder φ t ht hφt z).toAdd) hp
  have hsum :
      (∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd) = 0 := by
    simpa only [map_prod, map_zpow, toAdd_prod,
      toAdd_zpow, map_one, toAdd_one] using hmap
  calc
    (∑ i ∈ s, (ε i : K) * φ (L i)) =
        ∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvi : ((v i : Oˣ) : O) = 1 + t * L i := by
        rw [hv i hi]
        exact hrep i hi
      rw [actualFirstOrder_apply_of_eq φ t ht hφt (v i) hvi, zsmul_eq_mul]
    _ = 0 := hsum

end Domain

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uO,uK,uIota} : type_of% @_root_.OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one.{uO,uK,uIota} := @_root_.OAI.CirculantHadamard.first_order_sum_eq_zero_of_prod_eq_one.{uO,uK,uIota}
