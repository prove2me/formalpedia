-- Prove2me | solution 1 for OAI.PiExponent.exists_successive_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T10:34:21.345578+00:00
-- url     : https://prove2.me/submissions/8cb9cca0-10a2-41e4-bdce-ead94ea9f091

import Lean
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_exists_large_log_approximation

section



namespace OAI

namespace PiExponent



















end PiExponent

end OAI

end
section
open OAI OAI.PiExponent


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
theorem solution
    (nu : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))
    (T : List ℝ → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
      2 ≤ q n ∧ p n ≠ 0 ∧
      |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
      1 ≤ Nat.ceil (Real.log (q n)) ∧
      T (((List.range n).reverse).map
        (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
          ((Nat.ceil (Real.log (q n))) : ℝ) := open OAI OAI.PiExponent in by
  classical
  let wt : ℤ × ℕ → ℝ := fun a => (Nat.ceil (Real.log a.2) : ℝ)
  let Good : ℤ × ℕ → Prop := fun a =>
    2 ≤ a.2 ∧ a.1 ≠ 0 ∧
    |Real.pi - (a.1 : ℝ) / a.2| ≤ (a.2 : ℝ) ^ (-nu) ∧
    1 ≤ Nat.ceil (Real.log a.2)
  have hex (L : List (ℤ × ℕ)) :
      ∃ a : ℤ × ℕ, Good a ∧ T (L.map wt) < wt a := by
    obtain ⟨p, q, hq, hlog, hp, happ⟩ :=
      OAI.PiExponent.exists_large_log_approximation nu (max 1 (T (L.map wt))) hnu hbad
    have hceil : Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) := Nat.le_ceil _
    have hone : 1 < (Nat.ceil (Real.log q) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlog hceil)
    have hnat : 1 ≤ Nat.ceil (Real.log q) := by exact_mod_cast le_of_lt hone
    exact ⟨(p, q), ⟨hq, hp, happ, hnat⟩,
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlog hceil)⟩
  let next : List (ℤ × ℕ) → ℤ × ℕ := fun L => (hex L).choose
  have hnext (L : List (ℤ × ℕ)) : Good (next L) ∧ T (L.map wt) < wt (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List (ℤ × ℕ) := Nat.rec [] (fun _ L => next L :: L)
  let a : ℕ → ℤ × ℕ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change a n :: hist n = (List.range (n + 1)).reverse.map a
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨fun n => (a n).1, fun n => (a n).2, fun n => ?_⟩
  have hgood : Good (a n) := (hnext (hist n)).1
  refine ⟨hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2, ?_⟩
  have hbound := (hnext (hist n)).2
  have hmap : (hist n).map wt = (List.range n).reverse.map (wt ∘ a) := by
    rw [hhist, List.map_map]
  rw [hmap] at hbound
  exact hbound

end

#print axioms solution
