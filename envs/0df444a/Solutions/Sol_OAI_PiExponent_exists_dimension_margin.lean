-- Prove2me | solution 1 for OAI.PiExponent.exists_dimension_margin
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T10:24:38.265542+00:00
-- url     : https://prove2.me/submissions/df79b761-8eb4-4d0f-a407-0a119572fcd2

import Definitions.Def_OAI_NumberTheory_PiExponent_LocalAlgebra_Dimension
import Lean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section


namespace OAI

open Filter Topology

namespace PiExponent

 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

end PiExponent

end OAI

end

section







namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

















theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le



theorem dimension_error_le (theta B C a b : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + 100 * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) (by norm_num)



theorem tendsto_dimension_error_majorant (theta B C a b : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      100 * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul 100)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]



end PiExponent

end

end OAI

end
noncomputable section
open OAI OAI.PiExponent
open Filter
open scoped Topology


open Lean Meta in
run_meta do
  let requests : Array (String × Lean.Name × String) := #[]
  let env ← Lean.getEnv
  let mut rows : Array Lean.Json := #[]
  let mut actualNames : Array Lean.Name := #[]
  for (sourceName, userName, expectedKind) in requests do
    let mut candidates : Array Lean.Name := #[]
    for (actualName, _) in env.constants.toList do
      if Lean.privateToUserName? actualName == some userName then
        if (env.getModuleIdxFor? actualName).isNone then
          candidates := candidates.push actualName
    unless candidates.size == 1 do
      throwError "Expected one OwnModule private binding for {userName}, found {candidates.size}"
    let actualName := candidates[0]!
    let some ci := env.find? actualName | throwError "Missing recovered private declaration"
    let (kind, value, safety) ← match ci with
      | .thmInfo t => pure ("theorem", t.value, Lean.Json.null)
      | .defnInfo d => pure ("def", d.value, Lean.toJson (reprStr d.safety))
      | _ => throwError "Recovered private CI is neither theorem nor definition"
    unless kind == expectedKind do
      throwError "Recovered private CI kind differs from source Graph: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
        value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Recovered private CI type/value is not closed"
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Private helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
    rows := rows.push <| Lean.Json.mkObj [
      ("sourceGraphName", Lean.toJson sourceName),
      ("nodeGeneratedName", Lean.toJson userName.toString),
      ("actualKernelName", Lean.toJson actualName.toString),
      ("kind", Lean.toJson kind), ("safety", safety),
      ("ownerKind", Lean.toJson "OwnModule"),
      ("ownModule", Lean.toJson env.mainModule.toString),
      ("moduleIndexIsNone", Lean.toJson true),
      ("levelParams", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
      ("typeRefs", Lean.toJson (ci.type.getUsedConstants.map Lean.Name.toString)),
      ("valueRefs", Lean.toJson (value.getUsedConstants.map Lean.Name.toString)),
      ("snapshotValueRequired", Lean.toJson (kind == "def")),
      ("axioms", Lean.toJson (axioms.map Lean.Name.toString))]
  IO.println ("PI_ISOLATED_PRIVATE_MAP " ++ (Lean.Json.mkObj [
    ("artifact", Lean.toJson "Sol"),
    ("ownModule", Lean.toJson env.mainModule.toString),
    ("rows", Lean.Json.arr rows)]).compress)
theorem solution (theta A B C eta a b epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / OAI.PiExponent.dimensionV theta B C m +
        100 * (OAI.PiExponent.dimensionK C m : ℝ) / OAI.PiExponent.dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := open OAI OAI.PiExponent in by
  have herrors := (OAI.PiExponent.tendsto_dimension_error_majorant theta B C a b hB
    (zero_lt_one.trans hC) hsmall hlarge).eventually (gt_mem_nhds hepsilon)
  have hcollision := (OAI.PiExponent.tendsto_dimension_collision A B eta hratio heta).eventually
    (eventually_gt_atTop target)
  have hfloor := (tendsto_pow_atTop_atTop_of_one_lt hC).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgood : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      (a * (m : ℝ) + b) / OAI.PiExponent.dimensionV theta B C m +
        100 * (OAI.PiExponent.dimensionK C m : ℝ) / OAI.PiExponent.dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [herrors, hcollision, hfloor, eventually_ge_atTop 1]
      with m herror hcollision hfloor hm
    exact ⟨hm, (OAI.PiExponent.dimension_error_le theta B C a b htheta hB
      (zero_lt_one.trans hC).le ha hb m hfloor).trans_lt herror, hcollision⟩
  exact hgood.exists

end

#print axioms solution
