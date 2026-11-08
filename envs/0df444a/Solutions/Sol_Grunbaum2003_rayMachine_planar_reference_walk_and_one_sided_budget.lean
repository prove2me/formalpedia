-- Prove2me | solution 1 for Grunbaum2003.rayMachine_planar_reference_walk_and_one_sided_budget
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T18:41:34.950403+00:00
-- url     : https://prove2.me/submissions/abe88551-619c-4100-b509-d7308b16629a

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

noncomputable section

namespace Grunbaum2003

theorem nonneg_smul_frontier_mem_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ P ↔ s ≤ 1 := by
  constructor
  · intro hsb
    by_contra hle
    have hsone : 1 < s := lt_of_not_ge hle
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hinv : s⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_iff₀ hspos]
      simpa only [one_mul] using hsone
    have hi := hconv.combo_interior_self_mem_interior hzero hsb
      (sub_pos.mpr hinv) (inv_nonneg.mpr hspos.le) (sub_add_cancel 1 s⁻¹)
    have hbint : b ∈ interior P := by
      simpa only [smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hspos.ne', one_smul]
        using hi
    exact hb.2 hbint
  · intro hsone
    have hi := hconv (interior_subset hzero) (hclosed.frontier_subset hb)
      (sub_nonneg.mpr hsone) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

theorem frontier_eq_of_pos_smul {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b c : Fin d → ℝ} (hb : b ∈ frontier P) (hc : c ∈ frontier P)
    {s : ℝ} (hs : 0 < s) (hcb : c = s • b) : c = b := by
  have hsle : s ≤ 1 := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs.le).mp
    (hcb ▸ hclosed.frontier_subset hc)
  have hsge : 1 ≤ s := by
    by_contra h
    have hslt : s < 1 := lt_of_not_ge h
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hslt) hs.le (sub_add_cancel 1 s)
    have hcint : c ∈ interior P := by
      rw [hcb]
      simpa only [smul_zero, zero_add] using hi
    exact hc.2 hcint
  rw [hcb, le_antisymm hsle hsge, one_smul]

theorem rayOracle_eq_at_nonzero {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle₁ oracle₂ : (Fin d → ℝ) → (Fin d → ℝ)}
    (h₁ : IsPolytopeRayOracle P oracle₁) (h₂ : IsPolytopeRayOracle P oracle₂)
    {x : Fin d → ℝ} (hx : x ≠ 0) : oracle₁ x = oracle₂ x := by
  obtain ⟨hb, t, ht, hbt⟩ := h₁ x hx
  obtain ⟨hc, u, hu, hcu⟩ := h₂ x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hc hb (div_pos ht hu)
  rw [hbt, hcu, smul_smul, div_mul_cancel₀ t hu.ne']

theorem rayOracle_mem_iff_coordinate_ratio {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (x : Fin d → ℝ) (j : Fin d) (hxj : x j ≠ 0) :
    x ∈ P ↔ 1 ≤ oracle x j / x j := by
  have hx : x ≠ 0 := by
    intro h
    exact hxj (congrFun h j)
  obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
  have hxscale : x = t⁻¹ • oracle x := by
    rw [hbt, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hratio : oracle x j / x j = t := by
    rw [hbt]
    change (t * x j) / x j = t
    exact mul_div_cancel_right₀ t hxj
  rw [hratio, hxscale, nonneg_smul_frontier_mem_iff hconv hclosed hzero hb
    (inv_nonneg.mpr ht.le)]
  rw [inv_eq_one_div, div_le_iff₀ ht]
  simp only [one_mul]

theorem rayOracle_eq_self_iff_frontier {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) :
    oracle x = x ↔ x ∈ frontier P := by
  constructor
  · intro heq
    exact heq ▸ (horacle x hx).1
  · intro hxfront
    obtain ⟨hb, t, ht, hbt⟩ := horacle x hx
    exact frontier_eq_of_pos_smul hconv hclosed hzero hxfront hb ht hbt

end Grunbaum2003

namespace Grunbaum2003.RayPlanar

def suppliedPoint : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
def firstResponse (t : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then -t else t
def firstDirection : Fin 2 → ℝ := firstResponse 1
def secondDirection (t : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then t / (1 + t) else 2 / (1 + t)

private def chordNormal (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := (t - 1) * x 0 + t * x 1
  map_add' x y := by dsimp; ring
  map_smul' a x := by dsimp; ring

theorem secondDirection_geometry {t : ℝ} (ht : 0 < t) :
    0 < secondDirection t 0 ∧ 0 < secondDirection t 1 ∧
    secondDirection t ≠ 0 ∧
    suppliedPoint ∈ openSegment ℝ (firstResponse t) (secondDirection t) := by
  have hden : 0 < 1 + t := by linarith
  have hden' : 0 < t + 2 := by linarith
  have hx : 0 < secondDirection t 0 := div_pos ht hden
  have hy : 0 < secondDirection t 1 := div_pos (by norm_num) hden
  refine ⟨hx, hy, ?_, ?_⟩
  · intro h
    exact hx.ne' (congrFun h 0)
  · refine ⟨1 / (t + 2), (t + 1) / (t + 2), div_pos zero_lt_one hden',
      div_pos (by linarith) hden', ?_, ?_⟩
    · field_simp [hden'.ne']
      <;> ring
    · ext i
      fin_cases i <;>
        simp only [suppliedPoint, firstResponse, secondDirection, Fin.zero_eta,
          Fin.isValue, ite_true, Fin.mk_one, one_ne_zero, ite_false, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
      all_goals field_simp [hden.ne', hden'.ne'] <;> ring

theorem first_bracket_iff_fixed {P : Set (Fin 2 → ℝ)}
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) {t : ℝ} (ht : 0 < t) :
    suppliedPoint ∈ segment ℝ (firstResponse t) (oracle (secondDirection t)) ↔
      oracle (secondDirection t) = secondDirection t := by
  have hgeom := secondDirection_geometry ht
  obtain ⟨_, u, hu, hanswer⟩ := horacle (secondDirection t) hgeom.2.2.1
  have hNfirst : chordNormal t (firstResponse t) = t := by dsimp [chordNormal, firstResponse]; ring
  have hNpoint : chordNormal t suppliedPoint = t := by dsimp [chordNormal, suppliedPoint]; ring
  have hNsecond : chordNormal t (secondDirection t) = t := by
    dsimp [chordNormal, secondDirection]
    field_simp [(by linarith : (1 + t : ℝ) ≠ 0)]
    <;> ring
  have hNanswer : chordNormal t (oracle (secondDirection t)) = u * t := by
    rw [hanswer, map_smul, hNsecond, smul_eq_mul]
  constructor
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    have hbne : b ≠ 0 := by
      intro hbzero
      have haone : a = 1 := by linarith
      have heq' : firstResponse t = suppliedPoint := by
        simpa only [hbzero, haone, one_smul, zero_smul, add_zero] using heq
      have hx := congrFun heq' 0
      change -t = 0 at hx
      linarith
    have hN := congrArg (chordNormal t) heq
    simp only [map_add, map_smul, smul_eq_mul, hNfirst, hNanswer, hNpoint] at hN
    have hprod : (a + b * u - 1) * t = 0 := by nlinarith only [hN]
    have hnum : a + b * u - 1 = 0 := (mul_eq_zero.mp hprod).resolve_right ht.ne'
    have hbu : b * (u - 1) = 0 := by nlinarith only [hnum, hab]
    have huone : u = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hbu).resolve_left hbne)
    rw [hanswer, huone, one_smul]
  · intro hfixed
    rw [hfixed]
    exact openSegment_subset_segment ℝ _ _ hgeom.2.2.2

theorem first_query_response {P : Set (Fin 2 → ℝ)}
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    0 < oracle firstDirection 1 ∧
      oracle firstDirection = firstResponse (oracle firstDirection 1) := by
  have hdir : firstDirection ≠ 0 := by
    intro h
    have hx := congrFun h 0
    norm_num [firstDirection, firstResponse] at hx
  obtain ⟨_, t, ht, hanswer⟩ := horacle firstDirection hdir
  have hcoord : oracle firstDirection 1 = t := by
    rw [hanswer]
    simp only [firstDirection, firstResponse, Pi.smul_apply, smul_eq_mul,
      Fin.isValue, one_ne_zero, ite_false, mul_one]
  refine ⟨hcoord.symm ▸ ht, ?_⟩
  rw [hcoord, hanswer]
  ext i
  fin_cases i <;> norm_num [firstDirection, firstResponse]

theorem successful_first_bracket_face {P : Set (Fin 2 → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin 2 → ℝ) ∈ interior P)
    (hp : suppliedPoint ∈ frontier P)
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hbracket : suppliedPoint ∈
      segment ℝ (oracle firstDirection)
        (oracle (secondDirection (oracle firstDirection 1)))) :
    ∃ F : Set (Fin 2 → ℝ), IsExposed ℝ P F ∧ F ≠ P ∧
      suppliedPoint ∈ F ∧ oracle firstDirection ∈ F ∧
      oracle (secondDirection (oracle firstDirection 1)) ∈ F ∧
      oracle firstDirection ≠ oracle (secondDirection (oracle firstDirection 1)) := by
  obtain ⟨ht, hfirst⟩ := first_query_response horacle
  let t := oracle firstDirection 1
  have hgeom := secondDirection_geometry ht
  have hfixed : oracle (secondDirection t) = secondDirection t :=
    (first_bracket_iff_fixed horacle ht).mp (by simpa only [← hfirst] using hbracket)
  have hopen : suppliedPoint ∈
      openSegment ℝ (oracle firstDirection) (oracle (secondDirection t)) := by
    rw [hfirst, hfixed]
    exact hgeom.2.2.2
  have hleftP : oracle firstDirection ∈ P := by
    apply hclosed.frontier_subset
    exact (horacle firstDirection (by
      intro h; have hx := congrFun h 0; norm_num [firstDirection, firstResponse] at hx)).1
  have hrightP : oracle (secondDirection t) ∈ P :=
    hclosed.frontier_subset (horacle (secondDirection t) hgeom.2.2.1).1
  obtain ⟨l, hlne, hlmax⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hconv hp.2 ⟨0, hzero⟩
  have hlpoint : 0 < l suppliedPoint := by
    have hsub : l '' interior P ⊆ Set.Iic (l suppliedPoint) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hlmax x (interior_subset hx)
    have hopenImage : IsOpen (l '' interior P) := l.isOpenMap_of_ne_zero hlne _ isOpen_interior
    have hmem : (0 : ℝ) ∈ l '' interior P := ⟨0, hzero, map_zero l⟩
    have hmemInt : (0 : ℝ) ∈ interior (l '' interior P) := by
      rw [hopenImage.interior_eq]
      exact hmem
    have hi := interior_mono hsub hmemInt
    simpa only [interior_Iic, Set.mem_Iio] using hi
  let F := l.toExposed P
  have hF : IsExposed ℝ P F := ContinuousLinearMap.toExposed.isExposed
  have hpF : suppliedPoint ∈ F := ⟨hclosed.frontier_subset hp, hlmax⟩
  have hleftF := hF.isExtreme.left_mem_of_mem_openSegment hleftP hrightP hpF hopen
  have hrightF := hF.isExtreme.right_mem_of_mem_openSegment hleftP hrightP hpF hopen
  refine ⟨F, hF, ?_, hpF, hleftF, hrightF, ?_⟩
  · intro heq
    have hzF : (0 : Fin 2 → ℝ) ∈ F := heq.symm ▸ interior_subset hzero
    have hle := hzF.2 suppliedPoint (hclosed.frontier_subset hp)
    rw [map_zero] at hle
    exact (not_le_of_gt hlpoint) hle
  · change oracle firstDirection ≠ oracle (secondDirection t)
    intro heq
    have hx := congrFun heq 0
    have hleft : oracle firstDirection 0 = -t := congrFun hfirst 0
    have hright : oracle (secondDirection t) 0 = secondDirection t 0 := congrFun hfixed 0
    rw [hleft, hright] at hx
    linarith [hgeom.1]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def secondQueryProgram : List RayInstruction :=
  [.constant 2 1 1, .add 3 1 2 2, .div 0 1 3 3,
   .constant 2 2 4, .div 1 2 3 5, .query 6, .halt]

private theorem run_add_pdp {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih =>
    rw [Nat.succ_add]
    change (rayMachineStep program oracle c).bind (rayMachineRun program oracle (a + b)) =
      ((rayMachineStep program oracle c).bind (rayMachineRun program oracle a)).bind
        (rayMachineRun program oracle b)
    cases hs : rayMachineStep program oracle c with
    | none => rfl
    | some c' => exact ih c'

theorem secondQueryProgram_correct
    (oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (tape : ℤ → ℝ) (q : ℕ) (ht : 0 < tape 1) :
    ∃ c : RayConfiguration,
      rayMachineRun secondQueryProgram oracle 6
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      secondQueryProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (secondDirection (tape 1)) i) ∧
      c.tape 3 = tape 1 + 1 := by
  let t := tape 1
  have hden : t + 1 ≠ 0 := by dsimp [t]; linarith only [ht]
  let T₁ := Function.update tape (2 : ℤ) (1 : ℝ)
  let T₂ := Function.update T₁ (3 : ℤ) (t + 1)
  let T₃ := Function.update T₂ (0 : ℤ) (t / (t + 1))
  let T₄ := Function.update T₃ (2 : ℤ) (2 : ℝ)
  let T₅ := Function.update T₄ (1 : ℤ) (2 / (t + 1))
  let c₅ : RayConfiguration := {pc := 5, head := 0, tape := T₅, queries := q}
  have hrun₅ : rayMachineRun secondQueryProgram oracle 5
      {pc := 0, head := 0, tape := tape, queries := q} = some c₅ := by
    simp [rayMachineRun, rayMachineStep, secondQueryProgram, c₅,
      T₁, T₂, T₃, T₄, T₅, t, hden]
  have hinput : (fun i : Fin 2 => c₅.tape (c₅.head + (i.val : ℤ))) = secondDirection t := by
    ext i
    fin_cases i <;> simp [c₅, T₁, T₂, T₃, T₄, T₅, secondDirection, add_comm]
  have hdir : secondDirection t ≠ 0 := (secondDirection_geometry ht).2.2.1
  let c₆ : RayConfiguration := {c₅ with
    pc := 6
    queries := q + 1
    tape := fun j =>
      if h : 0 ≤ j - c₅.head ∧ j - c₅.head < (2 : ℤ) then
        oracle (secondDirection t) ⟨(j - c₅.head).toNat, by omega⟩
      else c₅.tape j}
  have hstep : rayMachineStep secondQueryProgram oracle c₅ = some c₆ := by
    have hpc : secondQueryProgram[c₅.pc]? = some (.query 6) := rfl
    simp only [rayMachineStep, hpc, hinput, if_neg hdir]
    rfl
  refine ⟨c₆, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · change rayMachineRun secondQueryProgram oracle (5 + 1) _ = _
    rw [run_add_pdp, hrun₅]
    simp only [Option.bind_some, rayMachineRun, hstep]
  · intro i
    have hi : 0 ≤ (i.val : ℤ) - c₅.head ∧ (i.val : ℤ) - c₅.head < (2 : ℤ) := by
      change 0 ≤ (i.val : ℤ) - 0 ∧ (i.val : ℤ) - 0 < 2
      omega
    change (if h : 0 ≤ (i.val : ℤ) - c₅.head ∧ (i.val : ℤ) - c₅.head < (2 : ℤ) then
      oracle (secondDirection t) ⟨((i.val : ℤ) - c₅.head).toNat, by omega⟩
      else c₅.tape (i.val : ℤ)) = _
    rw [dif_pos hi]
    congr 1
  · simp [c₆, c₅, T₁, T₂, T₃, T₄, T₅, t]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def firstMidpointDirection (t : ℝ) : Fin 2 → ℝ :=
  (1 / 2 : ℝ) • (suppliedPoint + secondDirection t)

private theorem smul_frontier_interior_iff {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {b : Fin d → ℝ} (hb : b ∈ frontier P) {s : ℝ} (hs : 0 ≤ s) :
    s • b ∈ interior P ↔ s < 1 := by
  constructor
  · intro hi
    have hle := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hb hs).mp
      (interior_subset hi)
    have hne : s ≠ 1 := by
      intro heq
      apply hb.2
      simpa only [heq, one_smul] using hi
    exact lt_of_le_of_ne hle hne
  · intro hlt
    have hi := hconv.combo_interior_self_mem_interior hzero (hclosed.frontier_subset hb)
      (sub_pos.mpr hlt) hs (sub_add_cancel 1 s)
    simpa only [smul_zero, zero_add] using hi

private def firstChordNormal (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := (t - 1) * x 0 + t * x 1
  map_add' x y := by dsimp; ring
  map_smul' a x := by dsimp; ring

theorem first_midpoint_strict_progress {P : Set (Fin 2 → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin 2 → ℝ) ∈ interior P)
    (hp : suppliedPoint ∈ frontier P)
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hnonfixed : oracle (secondDirection (oracle firstDirection 1)) ≠
      secondDirection (oracle firstDirection 1)) :
    let t := oracle firstDirection 1
    let r₂ := secondDirection t
    let r₃ := firstMidpointDirection t
    let p₂ := oracle r₂
    let p₃ := oracle r₃
    0 < r₃ 0 ∧ r₃ ≠ 0 ∧
    ∃ u₂ u₃ : ℝ, 0 < u₂ ∧ u₂ < 1 ∧ u₂ < u₃ ∧
      p₂ = u₂ • r₂ ∧ p₃ = u₃ • r₃ ∧
      u₂ = p₂ 0 / r₂ 0 ∧ u₃ = p₃ 0 / r₃ 0 ∧
      u₂ • r₃ ∈ interior P ∧
      0 < (t - 1) * (p₃ 0 - p₂ 0) + t * (p₃ 1 - p₂ 1) ∧
      (oracle firstDirection 0 - suppliedPoint 0) * (p₃ 1 - p₂ 1) -
        (oracle firstDirection 1 - suppliedPoint 1) * (p₃ 0 - p₂ 0) ≠ 0 := by
  dsimp only
  obtain ⟨ht, hfirst⟩ := first_query_response horacle
  let t := oracle firstDirection 1
  let r₂ := secondDirection t
  let r₃ := firstMidpointDirection t
  have hgeom := secondDirection_geometry ht
  have hmidpos : 0 < r₃ 0 := by
    change 0 < (1 / 2 : ℝ) * (0 + secondDirection t 0)
    exact mul_pos (by norm_num) (by simpa only [zero_add] using hgeom.1)
  have hmidne : r₃ ≠ 0 := by
    intro heq
    exact hmidpos.ne' (congrFun heq 0)
  obtain ⟨hp₂, u₂, hu₂, hreply₂⟩ := horacle r₂ hgeom.2.2.1
  obtain ⟨hp₃, u₃, hu₃, hreply₃⟩ := horacle r₃ hmidne
  have hleftP : firstResponse t ∈ P := by
    have hdir : firstDirection ≠ 0 := by
      intro heq
      have hx := congrFun heq 0
      norm_num [firstDirection, firstResponse] at hx
    have hi := hclosed.frontier_subset (horacle firstDirection hdir).1
    rwa [hfirst] at hi
  have hu₂le : u₂ ≤ 1 := by
    by_contra hle
    have hgt : 1 < u₂ := lt_of_not_ge hle
    have hinvlt : u₂⁻¹ < 1 := by
      rw [inv_eq_one_div, div_lt_one hu₂]
      exact hgt
    have hr₂int : r₂ ∈ interior P := by
      have hi := (smul_frontier_interior_iff hconv hclosed hzero hp₂
        (inv_nonneg.mpr hu₂.le)).mpr hinvlt
      have heq : u₂⁻¹ • oracle r₂ = r₂ := by
        rw [hreply₂, smul_smul, inv_mul_cancel₀ hu₂.ne', one_smul]
      rwa [heq] at hi
    exact hp.2 (hconv.openSegment_self_interior_subset_interior hleftP hr₂int hgeom.2.2.2)
  have hu₂ne : u₂ ≠ 1 := by
    intro heq
    apply hnonfixed
    simpa only [heq, one_smul] using hreply₂
  have hu₂lt : u₂ < 1 := lt_of_le_of_ne hu₂le hu₂ne
  have hupint : u₂ • suppliedPoint ∈ interior P :=
    (smul_frontier_interior_iff hconv hclosed hzero hp hu₂.le).mpr hu₂lt
  have hcombo : (1 / 2 : ℝ) • (u₂ • suppliedPoint) +
      (1 / 2 : ℝ) • oracle r₂ ∈ interior P :=
    hconv.combo_interior_self_mem_interior hupint (hclosed.frontier_subset hp₂)
      (by norm_num) (by norm_num) (by norm_num)
  have hmidscale : u₂ • r₃ =
      (1 / 2 : ℝ) • (u₂ • suppliedPoint) + (1 / 2 : ℝ) • oracle r₂ := by
    rw [hreply₂]
    ext i
    change u₂ * ((1 / 2 : ℝ) * (suppliedPoint i + r₂ i)) =
      (1 / 2 : ℝ) * (u₂ * suppliedPoint i) + (1 / 2 : ℝ) * (u₂ * r₂ i)
    ring
  have hmidint : u₂ • r₃ ∈ interior P := hmidscale.symm ▸ hcombo
  have hrelint : (u₂ / u₃) • oracle r₃ ∈ interior P := by
    have heq : (u₂ / u₃) • oracle r₃ = u₂ • r₃ := by
      rw [hreply₃, smul_smul, div_mul_cancel₀ u₂ hu₃.ne']
    exact heq.symm ▸ hmidint
  have hratioLt : u₂ / u₃ < 1 :=
    (smul_frontier_interior_iff hconv hclosed hzero hp₃ (div_pos hu₂ hu₃).le).mp hrelint
  have hprogress : u₂ < u₃ := (div_lt_one hu₃).mp hratioLt
  have hNpoint : firstChordNormal t suppliedPoint = t := by
    dsimp [firstChordNormal, suppliedPoint]
    ring
  have hNr₂ : firstChordNormal t r₂ = t := by
    dsimp [firstChordNormal, r₂, secondDirection]
    field_simp [(by linarith only [ht] : (1 + t : ℝ) ≠ 0)]
    <;> ring
  have hNr₃ : firstChordNormal t r₃ = t := by
    change firstChordNormal t ((1 / 2 : ℝ) • (suppliedPoint + r₂)) = t
    rw [map_smul, map_add, hNpoint, hNr₂, smul_eq_mul]
    ring
  have hNdiff : firstChordNormal t (oracle r₃ - oracle r₂) = (u₃ - u₂) * t := by
    rw [map_sub, hreply₃, hreply₂, map_smul, map_smul, hNr₃, hNr₂, smul_eq_mul, smul_eq_mul]
    ring
  have hnormalPos : 0 < (t - 1) * (oracle r₃ 0 - oracle r₂ 0) +
      t * (oracle r₃ 1 - oracle r₂ 1) := by
    change 0 < firstChordNormal t (oracle r₃ - oracle r₂)
    rw [hNdiff]
    exact mul_pos (sub_pos.mpr hprogress) ht
  have hdet : (oracle firstDirection 0 - suppliedPoint 0) * (oracle r₃ 1 - oracle r₂ 1) -
      (oracle firstDirection 1 - suppliedPoint 1) * (oracle r₃ 0 - oracle r₂ 0) ≠ 0 := by
    have hfirst₀ : oracle firstDirection 0 = -t := congrFun hfirst 0
    have heq : (oracle firstDirection 0 - suppliedPoint 0) * (oracle r₃ 1 - oracle r₂ 1) -
        (oracle firstDirection 1 - suppliedPoint 1) * (oracle r₃ 0 - oracle r₂ 0) =
        -((t - 1) * (oracle r₃ 0 - oracle r₂ 0) + t * (oracle r₃ 1 - oracle r₂ 1)) := by
      rw [hfirst₀]
      change (-t - 0) * (oracle r₃ 1 - oracle r₂ 1) -
        (t - 1) * (oracle r₃ 0 - oracle r₂ 0) = _
      ring
    rw [heq]
    exact neg_ne_zero.mpr hnormalPos.ne'
  refine ⟨hmidpos, hmidne, u₂, u₃, hu₂, hu₂lt, hprogress, hreply₂, hreply₃,
    ?_, ?_, hmidint, hnormalPos, hdet⟩
  · rw [hreply₂]
    change u₂ = (u₂ * r₂ 0) / r₂ 0
    exact (mul_div_cancel_right₀ u₂ hgeom.1.ne').symm
  · rw [hreply₃]
    change u₃ = (u₃ * r₃ 0) / r₃ 0
    exact (mul_div_cancel_right₀ u₃ hmidpos.ne').symm

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def firstMidpointProgram : List RayInstruction :=
  [.constant 7 0 1, .add 5 0 7 2, .add 6 1 7 3, .constant 7 1 4,
   .sub 8 3 7 5, .div 0 8 3 6, .constant 7 2 7, .div 0 0 7 8,
   .add 8 3 7 9, .div 1 8 3 10, .div 1 1 7 11, .query 12, .halt]

private theorem run_add_fmp {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih =>
    rw [Nat.succ_add]
    change (rayMachineStep program oracle c).bind (rayMachineRun program oracle (a + b)) =
      ((rayMachineStep program oracle c).bind (rayMachineRun program oracle a)).bind
        (rayMachineRun program oracle b)
    cases hs : rayMachineStep program oracle c with
    | none => rfl
    | some c' => exact ih c'

theorem firstMidpointProgram_correct
    (oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (tape : ℤ → ℝ) (q : ℕ) (hD : 1 < tape 3) :
    ∃ c : RayConfiguration,
      rayMachineRun firstMidpointProgram oracle 12
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      firstMidpointProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) =
        oracle (firstMidpointDirection (tape 3 - 1)) i) ∧
      c.tape 5 = tape 0 ∧ c.tape 6 = tape 1 ∧ c.tape 3 = tape 3 := by
  let D := tape 3
  have hDne : D ≠ 0 := by dsimp [D]; linarith only [hD]
  let T₁ := Function.update tape (7 : ℤ) (0 : ℝ)
  let T₂ := Function.update T₁ (5 : ℤ) (tape 0)
  let T₃ := Function.update T₂ (6 : ℤ) (tape 1)
  let T₄ := Function.update T₃ (7 : ℤ) (1 : ℝ)
  let T₅ := Function.update T₄ (8 : ℤ) (D - 1)
  let T₆ := Function.update T₅ (0 : ℤ) ((D - 1) / D)
  let T₇ := Function.update T₆ (7 : ℤ) (2 : ℝ)
  let T₈ := Function.update T₇ (0 : ℤ) (((D - 1) / D) / 2)
  let T₉ := Function.update T₈ (8 : ℤ) (D + 2)
  let T₁₀ := Function.update T₉ (1 : ℤ) ((D + 2) / D)
  let T₁₁ := Function.update T₁₀ (1 : ℤ) (((D + 2) / D) / 2)
  let c₁₁ : RayConfiguration := {pc := 11, head := 0, tape := T₁₁, queries := q}
  have hrun : rayMachineRun firstMidpointProgram oracle 11
      {pc := 0, head := 0, tape := tape, queries := q} = some c₁₁ := by
    simp [rayMachineRun, rayMachineStep, firstMidpointProgram, c₁₁,
      T₁, T₂, T₃, T₄, T₅, T₆, T₇, T₈, T₉, T₁₀, T₁₁, D, hDne]
  have hinput : (fun i : Fin 2 => c₁₁.tape (c₁₁.head + (i.val : ℤ))) =
      firstMidpointDirection (D - 1) := by
    ext i
    fin_cases i <;>
      simp [c₁₁, T₁, T₂, T₃, T₄, T₅, T₆, T₇, T₈, T₉, T₁₀, T₁₁,
        firstMidpointDirection, suppliedPoint, secondDirection]
    all_goals field_simp [hDne] <;> ring
  have hdir : firstMidpointDirection (D - 1) ≠ 0 := by
    have hpositive : 0 < firstMidpointDirection (D - 1) 0 := by
      change 0 < (1 / 2 : ℝ) * (0 + secondDirection (D - 1) 0)
      exact mul_pos (by norm_num)
        (by simpa only [zero_add] using
          (secondDirection_geometry (by dsimp [D]; linarith only [hD] : 0 < D - 1)).1)
    intro heq
    exact hpositive.ne' (congrFun heq 0)
  let c₁₂ : RayConfiguration := {c₁₁ with
    pc := 12
    queries := q + 1
    tape := fun j =>
      if h : 0 ≤ j - c₁₁.head ∧ j - c₁₁.head < (2 : ℤ) then
        oracle (firstMidpointDirection (D - 1)) ⟨(j - c₁₁.head).toNat, by omega⟩
      else c₁₁.tape j}
  have hstep : rayMachineStep firstMidpointProgram oracle c₁₁ = some c₁₂ := by
    have hpc : firstMidpointProgram[c₁₁.pc]? = some (.query 12) := rfl
    simp only [rayMachineStep, hpc, hinput, if_neg hdir]
    rfl
  refine ⟨c₁₂, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · change rayMachineRun firstMidpointProgram oracle (11 + 1) _ = _
    rw [run_add_fmp, hrun]
    simp only [Option.bind_some, rayMachineRun, hstep]
  · intro i
    have hi : 0 ≤ (i.val : ℤ) - c₁₁.head ∧ (i.val : ℤ) - c₁₁.head < (2 : ℤ) := by
      change 0 ≤ (i.val : ℤ) - 0 ∧ (i.val : ℤ) - 0 < 2
      omega
    change (if h : 0 ≤ (i.val : ℤ) - c₁₁.head ∧ (i.val : ℤ) - c₁₁.head < (2 : ℤ) then
      oracle (firstMidpointDirection (D - 1)) ⟨((i.val : ℤ) - c₁₁.head).toNat, by omega⟩
      else c₁₁.tape (i.val : ℤ)) = _
    rw [dif_pos hi]
    congr 1
  all_goals simp [c₁₂, c₁₁, T₁, T₂, T₃, T₄, T₅, T₆, T₇, T₈, T₉, T₁₀, T₁₁, D]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def firstChordValue (t : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (t - 1) * x 0 + t * x 1

def firstIntersectionParameter (t : ℝ) (p₂ p₃ : Fin 2 → ℝ) : ℝ :=
  (t - firstChordValue t p₂) / firstChordValue t (p₃ - p₂)

def firstIntersectionDirection (t : ℝ) (p₂ p₃ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  p₂ + firstIntersectionParameter t p₂ p₃ • (p₃ - p₂)

private def firstChordLinear (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun := firstChordValue t
  map_add' x y := by dsimp [firstChordValue]; ring
  map_smul' a x := by dsimp [firstChordValue]; ring

theorem first_chord_intersection_data {P : Set (Fin 2 → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin 2 → ℝ) ∈ interior P)
    (hp : suppliedPoint ∈ frontier P)
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hnonfixed : oracle (secondDirection (oracle firstDirection 1)) ≠
      secondDirection (oracle firstDirection 1)) :
    let t := oracle firstDirection 1
    let p₂ := oracle (secondDirection t)
    let p₃ := oracle (firstMidpointDirection t)
    0 < firstChordValue t (p₃ - p₂) ∧
      firstIntersectionDirection t p₂ p₃ ≠ 0 ∧
      firstChordValue t (firstIntersectionDirection t p₂ p₃) = t ∧
      ∀ s : ℝ, firstChordValue t (p₂ + s • (p₃ - p₂)) = t ↔
        s = firstIntersectionParameter t p₂ p₃ := by
  dsimp only
  let t := oracle firstDirection 1
  let p₂ := oracle (secondDirection t)
  let p₃ := oracle (firstMidpointDirection t)
  obtain ⟨ht, _⟩ := first_query_response horacle
  obtain ⟨_, _, u₂, u₃, _, _, _, _, _, _, _, _, hpos, _⟩ :=
    first_midpoint_strict_progress hconv hclosed hzero hp horacle hnonfixed
  have hdenpos : 0 < firstChordValue t (p₃ - p₂) := hpos
  have hden : firstChordValue t (p₃ - p₂) ≠ 0 := hdenpos.ne'
  have hpoint : firstChordValue t (firstIntersectionDirection t p₂ p₃) = t := by
    change firstChordLinear t
      (p₂ + firstIntersectionParameter t p₂ p₃ • (p₃ - p₂)) = t
    rw [map_add, map_smul, smul_eq_mul]
    change firstChordValue t p₂ +
      ((t - firstChordValue t p₂) / firstChordValue t (p₃ - p₂)) *
        firstChordValue t (p₃ - p₂) = t
    rw [div_mul_cancel₀ _ hden]
    ring
  refine ⟨hdenpos, ?_, hpoint, ?_⟩
  · intro heq
    rw [heq] at hpoint
    change (t - 1) * 0 + t * 0 = t at hpoint
    have : t = 0 := by simpa only [mul_zero, add_zero] using hpoint.symm
    exact ht.ne' this
  · intro s
    change firstChordLinear t (p₂ + s • (p₃ - p₂)) = t ↔
      s = firstIntersectionParameter t p₂ p₃
    rw [map_add, map_smul, smul_eq_mul]
    change firstChordValue t p₂ + s * firstChordValue t (p₃ - p₂) = t ↔
      s = (t - firstChordValue t p₂) / firstChordValue t (p₃ - p₂)
    rw [eq_div_iff hden]
    constructor <;> intro heq <;> linarith only [heq]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def referenceWalkProgram : List RayInstruction :=
  [.constant 2 0 1,
   .add 9 0 2 2,
   .add 10 1 2 3,
   .constant 7 1 4,
   .sub 8 3 7 5,
   .sub 11 9 5 6,
   .sub 12 10 6 7,
   .sub 15 8 7 8,
   .mul 13 15 5 9,
   .mul 16 8 6 10,
   .add 13 13 16 11,
   .mul 14 15 11 12,
   .mul 16 8 12 13,
   .add 14 14 16 14,
   .sub 15 8 13 15,
   .div 15 15 14 16,
   .mul 0 15 11 17,
   .add 0 5 0 18,
   .mul 1 15 12 19,
   .add 1 6 1 20,
   .add 16 13 14 21,
   .sub 16 16 8 22,
   .branch 16 23 27 23,
   .branch 0 24 27 24,
   .query 25,
   .add 5 9 2 26,
   .add 6 10 2 0,
   .halt]

private def tapePoint_rwp (tape : ℤ → ℝ) (i j : ℤ) : Fin 2 → ℝ :=
  fun k => if k = 0 then tape i else tape j

private theorem run_add_rwp {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih =>
    rw [Nat.succ_add]
    change (rayMachineStep program oracle c).bind (rayMachineRun program oracle (a + b)) =
      ((rayMachineStep program oracle c).bind (rayMachineRun program oracle a)).bind
        (rayMachineRun program oracle b)
    cases hs : rayMachineStep program oracle c with
    | none => rfl
    | some c' => exact ih c'

theorem referenceWalkProgram_one_iteration
    (oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (tape : ℤ → ℝ) (q : ℕ) (hD : 1 < tape 3)
    (hδ : firstChordValue (tape 3 - 1)
      (tapePoint_rwp tape 0 1 - tapePoint_rwp tape 5 6) ≠ 0) :
    let t := tape 3 - 1
    let p₂ := tapePoint_rwp tape 5 6
    let p₃ := tapePoint_rwp tape 0 1
    let δ := firstChordValue t (p₃ - p₂)
    let test := firstChordValue t p₂ + δ - t
    let r := firstIntersectionDirection t p₂ p₃
    ∃ c : RayConfiguration,
      rayMachineRun referenceWalkProgram oracle 27
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) =
        if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
      c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
      c.tape 14 = δ ∧ c.tape 16 = test ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := by
  dsimp only
  let t := tape 3 - 1
  let p₂ := tapePoint_rwp tape 5 6
  let p₃ := tapePoint_rwp tape 0 1
  let a := firstChordValue t p₂
  let δ := firstChordValue t (p₃ - p₂)
  let s := firstIntersectionParameter t p₂ p₃
  let test := a + δ - t
  let r := firstIntersectionDirection t p₂ p₃
  change ∃ c : RayConfiguration,
    rayMachineRun referenceWalkProgram oracle 27
      {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
    c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
    c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
    (∀ i : Fin 2, c.tape (i.val : ℤ) = if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
    c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
    c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
    c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
    c.tape 14 = δ ∧ c.tape 16 = test ∧
    (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j)
  have ht : 0 < t := by dsimp [t]; linarith only [hD]
  have hden : δ ≠ 0 := hδ
  have hdenTape : (tape 3 - 1 - 1) * (tape 0 - tape 5) +
      (tape 3 - 1) * (tape 1 - tape 6) ≠ 0 := by
    simpa [δ, t, p₂, p₃, firstChordValue, tapePoint_rwp] using hden
  have hrValue : firstChordValue t r = t := by
    change (t - 1) * (p₂ 0 + s * (p₃ 0 - p₂ 0)) +
      t * (p₂ 1 + s * (p₃ 1 - p₂ 1)) = t
    have hmul : s * δ = t - a := div_mul_cancel₀ _ hden
    dsimp [δ, a, firstChordValue] at hmul
    nlinarith only [hmul]
  have hrne : r ≠ 0 := by
    intro heq
    rw [heq] at hrValue
    change (t - 1) * 0 + t * 0 = t at hrValue
    have : t = 0 := by simpa only [mul_zero, add_zero] using hrValue.symm
    exact ht.ne' this
  let T1 := Function.update tape (2 : ℤ) (0 : ℝ)
  let T2 := Function.update T1 (9 : ℤ) (tape 0 : ℝ)
  let T3 := Function.update T2 (10 : ℤ) (tape 1 : ℝ)
  let T4 := Function.update T3 (7 : ℤ) (1 : ℝ)
  let T5 := Function.update T4 (8 : ℤ) (t : ℝ)
  let T6 := Function.update T5 (11 : ℤ) (p₃ 0 - p₂ 0 : ℝ)
  let T7 := Function.update T6 (12 : ℤ) (p₃ 1 - p₂ 1 : ℝ)
  let T8 := Function.update T7 (15 : ℤ) (t - 1 : ℝ)
  let T9 := Function.update T8 (13 : ℤ) ((t - 1) * p₂ 0 : ℝ)
  let T10 := Function.update T9 (16 : ℤ) (t * p₂ 1 : ℝ)
  let T11 := Function.update T10 (13 : ℤ) (a : ℝ)
  let T12 := Function.update T11 (14 : ℤ) ((t - 1) * (p₃ 0 - p₂ 0) : ℝ)
  let T13 := Function.update T12 (16 : ℤ) (t * (p₃ 1 - p₂ 1) : ℝ)
  let T14 := Function.update T13 (14 : ℤ) (δ : ℝ)
  let T15 := Function.update T14 (15 : ℤ) (t - a : ℝ)
  let T16 := Function.update T15 (15 : ℤ) (s : ℝ)
  let T17 := Function.update T16 (0 : ℤ) (s * (p₃ 0 - p₂ 0) : ℝ)
  let T18 := Function.update T17 (0 : ℤ) (p₂ 0 + s * (p₃ 0 - p₂ 0) : ℝ)
  let T19 := Function.update T18 (1 : ℤ) (s * (p₃ 1 - p₂ 1) : ℝ)
  let T20 := Function.update T19 (1 : ℤ) (p₂ 1 + s * (p₃ 1 - p₂ 1) : ℝ)
  let T21 := Function.update T20 (16 : ℤ) (a + δ : ℝ)
  let T22 := Function.update T21 (16 : ℤ) (test : ℝ)
  have hframe22 : ∀ j : ℤ, j < 0 ∨ 16 < j → T22 j = tape j := by
    intro j hj
    have hne0 : j ≠ (0 : ℤ) := by omega
    have hne1 : j ≠ (1 : ℤ) := by omega
    have hne2 : j ≠ (2 : ℤ) := by omega
    have hne3 : j ≠ (3 : ℤ) := by omega
    have hne4 : j ≠ (4 : ℤ) := by omega
    have hne5 : j ≠ (5 : ℤ) := by omega
    have hne6 : j ≠ (6 : ℤ) := by omega
    have hne7 : j ≠ (7 : ℤ) := by omega
    have hne8 : j ≠ (8 : ℤ) := by omega
    have hne9 : j ≠ (9 : ℤ) := by omega
    have hne10 : j ≠ (10 : ℤ) := by omega
    have hne11 : j ≠ (11 : ℤ) := by omega
    have hne12 : j ≠ (12 : ℤ) := by omega
    have hne13 : j ≠ (13 : ℤ) := by omega
    have hne14 : j ≠ (14 : ℤ) := by omega
    have hne15 : j ≠ (15 : ℤ) := by omega
    have hne16 : j ≠ (16 : ℤ) := by omega
    simp only [T22, T21, T20, T19, T18, T17, T16, T15, T14, T13, T12, T11, T10, T9, T8, T7, T6, T5, T4, T3, T2, T1, Function.update_of_ne hne0, Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3, Function.update_of_ne hne4, Function.update_of_ne hne5, Function.update_of_ne hne6, Function.update_of_ne hne7, Function.update_of_ne hne8, Function.update_of_ne hne9, Function.update_of_ne hne10, Function.update_of_ne hne11, Function.update_of_ne hne12, Function.update_of_ne hne13, Function.update_of_ne hne14, Function.update_of_ne hne15, Function.update_of_ne hne16]
  let c₂₂ : RayConfiguration := {pc := 22, head := 0, tape := T22, queries := q}
  let c₈ : RayConfiguration := {pc := 8, head := 0, tape := T8, queries := q}
  let c₁₆ : RayConfiguration := {pc := 16, head := 0, tape := T16, queries := q}
  have hrun₈ : rayMachineRun referenceWalkProgram oracle 8
      {pc := 0, head := 0, tape := tape, queries := q} = some c₈ := by
    simp [rayMachineRun, rayMachineStep, referenceWalkProgram, c₈,
      T1, T2, T3, T4, T5, T6, T7, T8, t, p₂, p₃, tapePoint_rwp]
  have hrun₁₆ : rayMachineRun referenceWalkProgram oracle 8 c₈ = some c₁₆ := by
    simp [rayMachineRun, rayMachineStep, referenceWalkProgram, c₈, c₁₆,
      T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, t, p₂, p₃, tapePoint_rwp, a, δ, s,
      firstIntersectionParameter, firstChordValue, hden, hdenTape]
  have hrun₂₂ : rayMachineRun referenceWalkProgram oracle 6 c₁₆ = some c₂₂ := by
    simp [rayMachineRun, rayMachineStep, referenceWalkProgram, c₁₆, c₂₂,
      T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, tapePoint_rwp, a, δ, s, test,
      firstIntersectionParameter, firstChordValue, hden, hdenTape]
  have hrun : rayMachineRun referenceWalkProgram oracle 22
      {pc := 0, head := 0, tape := tape, queries := q} = some c₂₂ := by
    change rayMachineRun referenceWalkProgram oracle (8 + (8 + 6)) _ = _
    rw [run_add_rwp, hrun₈]
    simp only [Option.bind_some]
    rw [run_add_rwp, hrun₁₆]
    simpa only [Option.bind_some] using hrun₂₂
  have hinput : (fun i : Fin 2 => c₂₂.tape (c₂₂.head + (i.val : ℤ))) = r := by
    ext i
    fin_cases i <;> simp [c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, r, s, firstIntersectionDirection, tapePoint_rwp, p₂, p₃]
  have hflag : c₂₂.tape (c₂₂.head + 16) = test := by
    simp [c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
  have hbranch : rayMachineStep referenceWalkProgram oracle c₂₂ =
      some {c₂₂ with pc := if test = 0 then 27 else 23} := by
    have hpc : referenceWalkProgram[c₂₂.pc]? = some (.branch 16 23 27 23) := rfl
    simp only [rayMachineStep, hpc, hflag]
    by_cases heq : test = 0
    · simp only [heq, lt_self_iff_false, if_false, if_true]
    · by_cases hneg : test < 0 <;> simp only [hneg, heq, if_true, if_false]

  let c₂₃ : RayConfiguration := {c₂₂ with pc := 23}
  have hinput₂₃ : (fun i : Fin 2 => c₂₃.tape (c₂₃.head + (i.val : ℤ))) = r := hinput
  have hflag₀ : c₂₃.tape (c₂₃.head + 0) = r 0 := congrFun hinput₂₃ 0
  have hbranch₂ : rayMachineStep referenceWalkProgram oracle c₂₃ =
      some {c₂₃ with pc := if r 0 = 0 then 27 else 24} := by
    have hpc : referenceWalkProgram[c₂₃.pc]? = some (.branch 0 24 27 24) := rfl
    simp only [rayMachineStep, hpc, hflag₀]
    by_cases hz : r 0 = 0
    · simp only [hz, lt_self_iff_false, if_false, if_true]
    · by_cases hn : r 0 < 0 <;> simp only [hn, hz, if_true, if_false]
  by_cases hstop : test = 0 ∨ r 0 = 0
  · let c : RayConfiguration := {c₂₂ with pc := 27}
    have hhalt : rayMachineStep referenceWalkProgram oracle c = some c := by
      have hpc : referenceWalkProgram[c.pc]? = some .halt := rfl
      simp only [rayMachineStep, hpc]
    have htail : rayMachineRun referenceWalkProgram oracle 5 c₂₂ = some c := by
      by_cases hz : test = 0
      · have hb : rayMachineStep referenceWalkProgram oracle c₂₂ = some c := by
          simpa only [hz, if_true] using hbranch
        simp only [rayMachineRun, hb, hhalt, Option.bind_some]
      · have hrz : r 0 = 0 := hstop.resolve_left hz
        have hb : rayMachineStep referenceWalkProgram oracle c₂₂ = some c₂₃ := by
          simpa only [hz, if_false] using hbranch
        have hb₂ : rayMachineStep referenceWalkProgram oracle c₂₃ = some c := by
          simpa only [hrz, if_true] using hbranch₂
        simp only [rayMachineRun, hb, hb₂, hhalt, Option.bind_some]
    refine ⟨c, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change rayMachineRun referenceWalkProgram oracle (22 + 5) _ = _
      rw [run_add_rwp, hrun]
      simpa only [Option.bind_some] using htail
    · rw [if_pos hstop]
    · change q = q + (if test = 0 ∨ r 0 = 0 then 0 else 1)
      rw [if_pos hstop, Nat.add_zero]
    · intro i
      rw [if_pos hstop]
      simpa only [c, c₂₂, zero_add] using congrFun hinput i
    · rw [if_pos hstop]
      simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · rw [if_pos hstop]
      simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · intro j hj
      exact hframe22 j hj
  · have htest : test ≠ 0 := fun hz => hstop (Or.inl hz)
    have hrzero : r 0 ≠ 0 := fun hz => hstop (Or.inr hz)
    let c₂₄ : RayConfiguration := {c₂₂ with pc := 24}
    have hb : rayMachineStep referenceWalkProgram oracle c₂₂ = some c₂₃ := by
      simpa only [htest, if_false] using hbranch
    have hb₂ : rayMachineStep referenceWalkProgram oracle c₂₃ = some c₂₄ := by
      simpa only [hrzero, if_false] using hbranch₂
    have hinput₂₄ : (fun i : Fin 2 => c₂₄.tape (c₂₄.head + (i.val : ℤ))) = r := hinput
    let Tq : ℤ → ℝ := fun j =>
      if h : 0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ) then
        oracle r ⟨(j - c₂₄.head).toNat, by omega⟩ else c₂₄.tape j
    let c₂₅ : RayConfiguration := {c₂₄ with pc := 25, tape := Tq, queries := q + 1}
    have hquery : rayMachineStep referenceWalkProgram oracle c₂₄ = some c₂₅ := by
      have hpc : referenceWalkProgram[c₂₄.pc]? = some (.query 25) := rfl
      simp only [rayMachineStep, hpc, hinput₂₄, if_neg hrne]
      rfl
    let Tc₅ := Function.update Tq (5 : ℤ) (tape 0)
    let c₂₆ : RayConfiguration := {pc := 26, head := 0, tape := Tc₅, queries := q + 1}
    let Tc₆ := Function.update Tc₅ (6 : ℤ) (tape 1)
    let c : RayConfiguration := {pc := 0, head := 0, tape := Tc₆, queries := q + 1}
    have hcopy₅ : rayMachineStep referenceWalkProgram oracle c₂₅ = some c₂₆ := by
      have hpc : referenceWalkProgram[c₂₅.pc]? = some (.add 5 9 2 26) := rfl
      have h₉ : c₂₅.tape (c₂₅.head + 9) = tape 0 := by simp [c₂₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      have h₂ : c₂₅.tape (c₂₅.head + 2) = 0 := by simp [c₂₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      simp only [rayMachineStep, hpc, h₉, h₂, add_zero]
      rfl
    have hcopy₆ : rayMachineStep referenceWalkProgram oracle c₂₆ = some c := by
      have hpc : referenceWalkProgram[c₂₆.pc]? = some (.add 6 10 2 0) := rfl
      have h₁₀ : c₂₆.tape (c₂₆.head + 10) = tape 1 := by simp [c₂₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      have h₂ : c₂₆.tape (c₂₆.head + 2) = 0 := by simp [c₂₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      simp only [rayMachineStep, hpc, h₁₀, h₂, add_zero]
      rfl
    refine ⟨c, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change rayMachineRun referenceWalkProgram oracle (22 + 5) _ = _
      rw [run_add_rwp, hrun]
      simp only [Option.bind_some, rayMachineRun, hb, hb₂, hquery, hcopy₅, hcopy₆]
    · rw [if_neg hstop]
    · change q + 1 = q + (if test = 0 ∨ r 0 = 0 then 0 else 1)
      rw [if_neg hstop]
    · intro i
      rw [if_neg hstop]
      change c.tape (i.val : ℤ) = oracle r i
      fin_cases i <;> simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂]
    · rw [if_neg hstop]
      simp [c, Tc₆, Tc₅]
    · rw [if_neg hstop]
      simp [c, Tc₆]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · intro j hj
      have hne5 : j ≠ (5 : ℤ) := by omega
      have hne6 : j ≠ (6 : ℤ) := by omega
      have hn : ¬ (0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ)) := by
        change ¬ (0 ≤ j - 0 ∧ j - 0 < (2 : ℤ))
        omega
      change Function.update (Function.update Tq (5 : ℤ) (tape 0)) (6 : ℤ) (tape 1) j = tape j
      rw [Function.update_of_ne hne6, Function.update_of_ne hne5]
      change (if h : 0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ) then
        oracle r ⟨(j - c₂₄.head).toNat, by omega⟩ else c₂₄.tape j) = tape j
      rw [dif_neg hn]
      exact hframe22 j hj

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private def tapePoint_rwe (tape : ℤ → ℝ) (i j : ℤ) : Fin 2 → ℝ :=
  fun k => if k = 0 then tape i else tape j

private theorem run_add_rwe {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih =>
    rw [Nat.succ_add]
    change (rayMachineStep program oracle c).bind (rayMachineRun program oracle (a + b)) =
      ((rayMachineStep program oracle c).bind (rayMachineRun program oracle a)).bind
        (rayMachineRun program oracle b)
    cases hs : rayMachineStep program oracle c with
    | none => rfl
    | some c' => exact ih c'

theorem referenceWalkProgram_exit_iteration
    (program : List RayInstruction)
    (hprefix : ∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?)
    (oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (tape : ℤ → ℝ) (q : ℕ) (hD : 1 < tape 3)
    (hδ : firstChordValue (tape 3 - 1)
      (tapePoint_rwe tape 0 1 - tapePoint_rwe tape 5 6) ≠ 0) :
    let t := tape 3 - 1
    let p₂ := tapePoint_rwe tape 5 6
    let p₃ := tapePoint_rwe tape 0 1
    let δ := firstChordValue t (p₃ - p₂)
    let test := firstChordValue t p₂ + δ - t
    let r := firstIntersectionDirection t p₂ p₃
    ∃ c : RayConfiguration,
      rayMachineRun program oracle (if test = 0 then 23 else if r 0 = 0 then 24 else 27)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) =
        if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
      c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
      c.tape 14 = δ ∧ c.tape 16 = test ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := by
  dsimp only
  have hfetch0 : program[0]? = some (.constant 2 0 1) := by
    rw [hprefix 0 (by decide)]
    rfl
  have hfetch1 : program[1]? = some (.add 9 0 2 2) := by
    rw [hprefix 1 (by decide)]
    rfl
  have hfetch2 : program[2]? = some (.add 10 1 2 3) := by
    rw [hprefix 2 (by decide)]
    rfl
  have hfetch3 : program[3]? = some (.constant 7 1 4) := by
    rw [hprefix 3 (by decide)]
    rfl
  have hfetch4 : program[4]? = some (.sub 8 3 7 5) := by
    rw [hprefix 4 (by decide)]
    rfl
  have hfetch5 : program[5]? = some (.sub 11 9 5 6) := by
    rw [hprefix 5 (by decide)]
    rfl
  have hfetch6 : program[6]? = some (.sub 12 10 6 7) := by
    rw [hprefix 6 (by decide)]
    rfl
  have hfetch7 : program[7]? = some (.sub 15 8 7 8) := by
    rw [hprefix 7 (by decide)]
    rfl
  have hfetch8 : program[8]? = some (.mul 13 15 5 9) := by
    rw [hprefix 8 (by decide)]
    rfl
  have hfetch9 : program[9]? = some (.mul 16 8 6 10) := by
    rw [hprefix 9 (by decide)]
    rfl
  have hfetch10 : program[10]? = some (.add 13 13 16 11) := by
    rw [hprefix 10 (by decide)]
    rfl
  have hfetch11 : program[11]? = some (.mul 14 15 11 12) := by
    rw [hprefix 11 (by decide)]
    rfl
  have hfetch12 : program[12]? = some (.mul 16 8 12 13) := by
    rw [hprefix 12 (by decide)]
    rfl
  have hfetch13 : program[13]? = some (.add 14 14 16 14) := by
    rw [hprefix 13 (by decide)]
    rfl
  have hfetch14 : program[14]? = some (.sub 15 8 13 15) := by
    rw [hprefix 14 (by decide)]
    rfl
  have hfetch15 : program[15]? = some (.div 15 15 14 16) := by
    rw [hprefix 15 (by decide)]
    rfl
  have hfetch16 : program[16]? = some (.mul 0 15 11 17) := by
    rw [hprefix 16 (by decide)]
    rfl
  have hfetch17 : program[17]? = some (.add 0 5 0 18) := by
    rw [hprefix 17 (by decide)]
    rfl
  have hfetch18 : program[18]? = some (.mul 1 15 12 19) := by
    rw [hprefix 18 (by decide)]
    rfl
  have hfetch19 : program[19]? = some (.add 1 6 1 20) := by
    rw [hprefix 19 (by decide)]
    rfl
  have hfetch20 : program[20]? = some (.add 16 13 14 21) := by
    rw [hprefix 20 (by decide)]
    rfl
  have hfetch21 : program[21]? = some (.sub 16 16 8 22) := by
    rw [hprefix 21 (by decide)]
    rfl
  have hfetch22 : program[22]? = some (.branch 16 23 27 23) := by
    rw [hprefix 22 (by decide)]
    rfl
  have hfetch23 : program[23]? = some (.branch 0 24 27 24) := by
    rw [hprefix 23 (by decide)]
    rfl
  have hfetch24 : program[24]? = some (.query 25) := by
    rw [hprefix 24 (by decide)]
    rfl
  have hfetch25 : program[25]? = some (.add 5 9 2 26) := by
    rw [hprefix 25 (by decide)]
    rfl
  have hfetch26 : program[26]? = some (.add 6 10 2 0) := by
    rw [hprefix 26 (by decide)]
    rfl
  let t := tape 3 - 1
  let p₂ := tapePoint_rwe tape 5 6
  let p₃ := tapePoint_rwe tape 0 1
  let a := firstChordValue t p₂
  let δ := firstChordValue t (p₃ - p₂)
  let s := firstIntersectionParameter t p₂ p₃
  let test := a + δ - t
  let r := firstIntersectionDirection t p₂ p₃
  change ∃ c : RayConfiguration,
    rayMachineRun program oracle (if test = 0 then 23 else if r 0 = 0 then 24 else 27)
      {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
    c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
    c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
    (∀ i : Fin 2, c.tape (i.val : ℤ) = if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
    c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
    c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
    c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
    c.tape 14 = δ ∧ c.tape 16 = test ∧
    (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j)
  have ht : 0 < t := by dsimp [t]; linarith only [hD]
  have hden : δ ≠ 0 := hδ
  have hdenTape : (tape 3 - 1 - 1) * (tape 0 - tape 5) +
      (tape 3 - 1) * (tape 1 - tape 6) ≠ 0 := by
    simpa [δ, t, p₂, p₃, firstChordValue, tapePoint_rwe] using hden
  have hrValue : firstChordValue t r = t := by
    change (t - 1) * (p₂ 0 + s * (p₃ 0 - p₂ 0)) +
      t * (p₂ 1 + s * (p₃ 1 - p₂ 1)) = t
    have hmul : s * δ = t - a := div_mul_cancel₀ _ hden
    dsimp [δ, a, firstChordValue] at hmul
    nlinarith only [hmul]
  have hrne : r ≠ 0 := by
    intro heq
    rw [heq] at hrValue
    change (t - 1) * 0 + t * 0 = t at hrValue
    have : t = 0 := by simpa only [mul_zero, add_zero] using hrValue.symm
    exact ht.ne' this
  let T1 := Function.update tape (2 : ℤ) (0 : ℝ)
  let T2 := Function.update T1 (9 : ℤ) (tape 0 : ℝ)
  let T3 := Function.update T2 (10 : ℤ) (tape 1 : ℝ)
  let T4 := Function.update T3 (7 : ℤ) (1 : ℝ)
  let T5 := Function.update T4 (8 : ℤ) (t : ℝ)
  let T6 := Function.update T5 (11 : ℤ) (p₃ 0 - p₂ 0 : ℝ)
  let T7 := Function.update T6 (12 : ℤ) (p₃ 1 - p₂ 1 : ℝ)
  let T8 := Function.update T7 (15 : ℤ) (t - 1 : ℝ)
  let T9 := Function.update T8 (13 : ℤ) ((t - 1) * p₂ 0 : ℝ)
  let T10 := Function.update T9 (16 : ℤ) (t * p₂ 1 : ℝ)
  let T11 := Function.update T10 (13 : ℤ) (a : ℝ)
  let T12 := Function.update T11 (14 : ℤ) ((t - 1) * (p₃ 0 - p₂ 0) : ℝ)
  let T13 := Function.update T12 (16 : ℤ) (t * (p₃ 1 - p₂ 1) : ℝ)
  let T14 := Function.update T13 (14 : ℤ) (δ : ℝ)
  let T15 := Function.update T14 (15 : ℤ) (t - a : ℝ)
  let T16 := Function.update T15 (15 : ℤ) (s : ℝ)
  let T17 := Function.update T16 (0 : ℤ) (s * (p₃ 0 - p₂ 0) : ℝ)
  let T18 := Function.update T17 (0 : ℤ) (p₂ 0 + s * (p₃ 0 - p₂ 0) : ℝ)
  let T19 := Function.update T18 (1 : ℤ) (s * (p₃ 1 - p₂ 1) : ℝ)
  let T20 := Function.update T19 (1 : ℤ) (p₂ 1 + s * (p₃ 1 - p₂ 1) : ℝ)
  let T21 := Function.update T20 (16 : ℤ) (a + δ : ℝ)
  let T22 := Function.update T21 (16 : ℤ) (test : ℝ)
  have hframe22 : ∀ j : ℤ, j < 0 ∨ 16 < j → T22 j = tape j := by
    intro j hj
    have hne0 : j ≠ (0 : ℤ) := by omega
    have hne1 : j ≠ (1 : ℤ) := by omega
    have hne2 : j ≠ (2 : ℤ) := by omega
    have hne3 : j ≠ (3 : ℤ) := by omega
    have hne4 : j ≠ (4 : ℤ) := by omega
    have hne5 : j ≠ (5 : ℤ) := by omega
    have hne6 : j ≠ (6 : ℤ) := by omega
    have hne7 : j ≠ (7 : ℤ) := by omega
    have hne8 : j ≠ (8 : ℤ) := by omega
    have hne9 : j ≠ (9 : ℤ) := by omega
    have hne10 : j ≠ (10 : ℤ) := by omega
    have hne11 : j ≠ (11 : ℤ) := by omega
    have hne12 : j ≠ (12 : ℤ) := by omega
    have hne13 : j ≠ (13 : ℤ) := by omega
    have hne14 : j ≠ (14 : ℤ) := by omega
    have hne15 : j ≠ (15 : ℤ) := by omega
    have hne16 : j ≠ (16 : ℤ) := by omega
    simp only [T22, T21, T20, T19, T18, T17, T16, T15, T14, T13, T12, T11, T10, T9, T8, T7, T6, T5, T4, T3, T2, T1, Function.update_of_ne hne0, Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3, Function.update_of_ne hne4, Function.update_of_ne hne5, Function.update_of_ne hne6, Function.update_of_ne hne7, Function.update_of_ne hne8, Function.update_of_ne hne9, Function.update_of_ne hne10, Function.update_of_ne hne11, Function.update_of_ne hne12, Function.update_of_ne hne13, Function.update_of_ne hne14, Function.update_of_ne hne15, Function.update_of_ne hne16]
  let c₂₂ : RayConfiguration := {pc := 22, head := 0, tape := T22, queries := q}
  let c₈ : RayConfiguration := {pc := 8, head := 0, tape := T8, queries := q}
  let c₁₆ : RayConfiguration := {pc := 16, head := 0, tape := T16, queries := q}
  have hrun₈ : rayMachineRun program oracle 8
      {pc := 0, head := 0, tape := tape, queries := q} = some c₈ := by
    simp [rayMachineRun, rayMachineStep, hfetch0, hfetch1, hfetch2, hfetch3, hfetch4, hfetch5, hfetch6, hfetch7, hfetch8, hfetch9, hfetch10, hfetch11, hfetch12, hfetch13, hfetch14, hfetch15, hfetch16, hfetch17, hfetch18, hfetch19, hfetch20, hfetch21, hfetch22, hfetch23, hfetch24, hfetch25, hfetch26, c₈,
      T1, T2, T3, T4, T5, T6, T7, T8, t, p₂, p₃, tapePoint_rwe]
  have hrun₁₆ : rayMachineRun program oracle 8 c₈ = some c₁₆ := by
    simp [rayMachineRun, rayMachineStep, hfetch0, hfetch1, hfetch2, hfetch3, hfetch4, hfetch5, hfetch6, hfetch7, hfetch8, hfetch9, hfetch10, hfetch11, hfetch12, hfetch13, hfetch14, hfetch15, hfetch16, hfetch17, hfetch18, hfetch19, hfetch20, hfetch21, hfetch22, hfetch23, hfetch24, hfetch25, hfetch26, c₈, c₁₆,
      T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, t, p₂, p₃, tapePoint_rwe, a, δ, s,
      firstIntersectionParameter, firstChordValue, hden, hdenTape]
  have hrun₂₂ : rayMachineRun program oracle 6 c₁₆ = some c₂₂ := by
    simp [rayMachineRun, rayMachineStep, hfetch0, hfetch1, hfetch2, hfetch3, hfetch4, hfetch5, hfetch6, hfetch7, hfetch8, hfetch9, hfetch10, hfetch11, hfetch12, hfetch13, hfetch14, hfetch15, hfetch16, hfetch17, hfetch18, hfetch19, hfetch20, hfetch21, hfetch22, hfetch23, hfetch24, hfetch25, hfetch26, c₁₆, c₂₂,
      T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, tapePoint_rwe, a, δ, s, test,
      firstIntersectionParameter, firstChordValue, hden, hdenTape]
  have hrun : rayMachineRun program oracle 22
      {pc := 0, head := 0, tape := tape, queries := q} = some c₂₂ := by
    change rayMachineRun program oracle (8 + (8 + 6)) _ = _
    rw [run_add_rwe, hrun₈]
    simp only [Option.bind_some]
    rw [run_add_rwe, hrun₁₆]
    simpa only [Option.bind_some] using hrun₂₂
  have hinput : (fun i : Fin 2 => c₂₂.tape (c₂₂.head + (i.val : ℤ))) = r := by
    ext i
    fin_cases i <;> simp [c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, r, s, firstIntersectionDirection, tapePoint_rwe, p₂, p₃]
  have hflag : c₂₂.tape (c₂₂.head + 16) = test := by
    simp [c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
  have hbranch : rayMachineStep program oracle c₂₂ =
      some {c₂₂ with pc := if test = 0 then 27 else 23} := by
    have hpc : program[c₂₂.pc]? = some (.branch 16 23 27 23) := by
      change program[22]? = _
      rw [hprefix 22 (by decide)]
      rfl
    simp only [rayMachineStep, hpc, hflag]
    by_cases heq : test = 0
    · simp only [heq, lt_self_iff_false, if_false, if_true]
    · by_cases hneg : test < 0 <;> simp only [hneg, heq, if_true, if_false]

  let c₂₃ : RayConfiguration := {c₂₂ with pc := 23}
  have hinput₂₃ : (fun i : Fin 2 => c₂₃.tape (c₂₃.head + (i.val : ℤ))) = r := hinput
  have hflag₀ : c₂₃.tape (c₂₃.head + 0) = r 0 := congrFun hinput₂₃ 0
  have hbranch₂ : rayMachineStep program oracle c₂₃ =
      some {c₂₃ with pc := if r 0 = 0 then 27 else 24} := by
    have hpc : program[c₂₃.pc]? = some (.branch 0 24 27 24) := by
      change program[23]? = _
      rw [hprefix 23 (by decide)]
      rfl
    simp only [rayMachineStep, hpc, hflag₀]
    by_cases hz : r 0 = 0
    · simp only [hz, lt_self_iff_false, if_false, if_true]
    · by_cases hn : r 0 < 0 <;> simp only [hn, hz, if_true, if_false]
  by_cases hstop : test = 0 ∨ r 0 = 0
  · let c : RayConfiguration := {c₂₂ with pc := 27}
    refine ⟨c, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hz : test = 0
      · rw [if_pos hz]
        change rayMachineRun program oracle (22 + 1) _ = _
        rw [run_add_rwe, hrun, Option.bind_some]
        have hb : rayMachineStep program oracle c₂₂ = some c := by
          simpa only [hz, if_true] using hbranch
        simp only [rayMachineRun, hb, Option.bind_some]
      · have hrz : r 0 = 0 := hstop.resolve_left hz
        rw [if_neg hz, if_pos hrz]
        change rayMachineRun program oracle (22 + 2) _ = _
        rw [run_add_rwe, hrun, Option.bind_some]
        have hb : rayMachineStep program oracle c₂₂ = some c₂₃ := by
          simpa only [hz, if_false] using hbranch
        have hb₂ : rayMachineStep program oracle c₂₃ = some c := by
          simpa only [hrz, if_true] using hbranch₂
        simp only [rayMachineRun, hb, hb₂, Option.bind_some]
    · rw [if_pos hstop]
    · change q = q + (if test = 0 ∨ r 0 = 0 then 0 else 1)
      rw [if_pos hstop, Nat.add_zero]
    · intro i
      rw [if_pos hstop]
      simpa only [c, c₂₂, zero_add] using congrFun hinput i
    · rw [if_pos hstop]
      simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · rw [if_pos hstop]
      simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · simp [c, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · intro j hj
      exact hframe22 j hj
  · have htest : test ≠ 0 := fun hz => hstop (Or.inl hz)
    have hrzero : r 0 ≠ 0 := fun hz => hstop (Or.inr hz)
    let c₂₄ : RayConfiguration := {c₂₂ with pc := 24}
    have hb : rayMachineStep program oracle c₂₂ = some c₂₃ := by
      simpa only [htest, if_false] using hbranch
    have hb₂ : rayMachineStep program oracle c₂₃ = some c₂₄ := by
      simpa only [hrzero, if_false] using hbranch₂
    have hinput₂₄ : (fun i : Fin 2 => c₂₄.tape (c₂₄.head + (i.val : ℤ))) = r := hinput
    let Tq : ℤ → ℝ := fun j =>
      if h : 0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ) then
        oracle r ⟨(j - c₂₄.head).toNat, by omega⟩ else c₂₄.tape j
    let c₂₅ : RayConfiguration := {c₂₄ with pc := 25, tape := Tq, queries := q + 1}
    have hquery : rayMachineStep program oracle c₂₄ = some c₂₅ := by
      have hpc : program[c₂₄.pc]? = some (.query 25) := by
        change program[24]? = _
        rw [hprefix 24 (by decide)]
        rfl
      simp only [rayMachineStep, hpc, hinput₂₄, if_neg hrne]
      rfl
    let Tc₅ := Function.update Tq (5 : ℤ) (tape 0)
    let c₂₆ : RayConfiguration := {pc := 26, head := 0, tape := Tc₅, queries := q + 1}
    let Tc₆ := Function.update Tc₅ (6 : ℤ) (tape 1)
    let c : RayConfiguration := {pc := 0, head := 0, tape := Tc₆, queries := q + 1}
    have hcopy₅ : rayMachineStep program oracle c₂₅ = some c₂₆ := by
      have hpc : program[c₂₅.pc]? = some (.add 5 9 2 26) := by
        change program[25]? = _
        rw [hprefix 25 (by decide)]
        rfl
      have h₉ : c₂₅.tape (c₂₅.head + 9) = tape 0 := by simp [c₂₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      have h₂ : c₂₅.tape (c₂₅.head + 2) = 0 := by simp [c₂₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      simp only [rayMachineStep, hpc, h₉, h₂, add_zero]
      rfl
    have hcopy₆ : rayMachineStep program oracle c₂₆ = some c := by
      have hpc : program[c₂₆.pc]? = some (.add 6 10 2 0) := by
        change program[26]? = _
        rw [hprefix 26 (by decide)]
        rfl
      have h₁₀ : c₂₆.tape (c₂₆.head + 10) = tape 1 := by simp [c₂₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      have h₂ : c₂₆.tape (c₂₆.head + 2) = 0 := by simp [c₂₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
      simp only [rayMachineStep, hpc, h₁₀, h₂, add_zero]
      rfl
    refine ⟨c, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_neg htest, if_neg hrzero]
      change rayMachineRun program oracle (22 + 5) _ = _
      rw [run_add_rwe, hrun]
      simp only [Option.bind_some, rayMachineRun, hb, hb₂, hquery, hcopy₅, hcopy₆]
    · rw [if_neg hstop]
    · change q + 1 = q + (if test = 0 ∨ r 0 = 0 then 0 else 1)
      rw [if_neg hstop]
    · intro i
      rw [if_neg hstop]
      change c.tape (i.val : ℤ) = oracle r i
      fin_cases i <;> simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂]
    · rw [if_neg hstop]
      simp [c, Tc₆, Tc₅]
    · rw [if_neg hstop]
      simp [c, Tc₆]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · simp [c, Tc₆, Tc₅, Tq, c₂₄, c₂₂, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, t, p₂, p₃, a, δ, test]
    · intro j hj
      have hne5 : j ≠ (5 : ℤ) := by omega
      have hne6 : j ≠ (6 : ℤ) := by omega
      have hn : ¬ (0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ)) := by
        change ¬ (0 ≤ j - 0 ∧ j - 0 < (2 : ℤ))
        omega
      change Function.update (Function.update Tq (5 : ℤ) (tape 0)) (6 : ℤ) (tape 1) j = tape j
      rw [Function.update_of_ne hne6, Function.update_of_ne hne5]
      change (if h : 0 ≤ j - c₂₄.head ∧ j - c₂₄.head < (2 : ℤ) then
        oracle r ⟨(j - c₂₄.head).toNat, by omega⟩ else c₂₄.tape j) = tape j
      rw [dif_neg hn]
      exact hframe22 j hj

end Grunbaum2003.RayPlanar

namespace Grunbaum2003

theorem perturb_frontier_ne_zero_of_negative_mem {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P) : p + s • u ≠ 0 := by
  intro hz
  have hc : 0 ≤ s / a := div_nonneg hs ha.le
  have hc1 : s / a < 1 := (div_lt_one ha).mpr hsa
  have hi := hconv.combo_interior_self_mem_interior hzero hminus
    (sub_pos.mpr hc1) hc (sub_add_cancel 1 (s / a))
  have heq : (s / a) • ((-a) • u) = p := by
    ext j
    have hj := congrFun hz j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    field_simp
    nlinarith only [hj]
  have hpint : p ∈ interior P := by
    simpa only [smul_zero, zero_add, heq] using hi
  exact hp.2 hpint

theorem rayOracle_perturb_scale_upper {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hsa : s < a)
    (hminus : (-a) • u ∈ P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + s • u) = t • (p + s • u) ∧
      t * (a - s) ≤ a := by
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + s • u) hr
  refine ⟨t, ht, heq, ?_⟩
  have hden : 0 < a + t * s := add_pos_of_pos_of_nonneg ha (mul_nonneg ht.le hs)
  have hc : 0 ≤ a / (a + t * s) := div_nonneg ha.le hden.le
  have hc1 : a / (a + t * s) ≤ 1 := (div_le_one hden).mpr (by linarith [mul_nonneg ht.le hs])
  have hcombo := hconv (hclosed.frontier_subset hq) hminus hc
    (sub_nonneg.mpr hc1) (add_sub_cancel (a / (a + t * s)) 1)
  have hceq : (a / (a + t * s)) • oracle (p + s • u) +
      (1 - a / (a + t * s)) • ((-a) • u) =
      (t * a / (a + t * s)) • p := by
    rw [heq]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [hceq] at hcombo
  have hscaleNonneg : 0 ≤ t * a / (a + t * s) :=
    div_nonneg (mul_nonneg ht.le ha.le) hden.le
  have hscaleLe := (nonneg_smul_frontier_mem_iff hconv hclosed hzero hp hscaleNonneg).mp hcombo
  have hnum : t * a ≤ a + t * s := (div_le_one hden).mp hscaleLe
  nlinarith only [hnum]

theorem facet_local_step_bounds {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    0 < ε ∧ ε < a ∧ ε * (1 + a * M) < a * δ := by
  have haM : 0 ≤ a * M := mul_nonneg ha.le hM
  have hD : 0 < 2 * (1 + a * M + δ) := by linarith
  dsimp only
  refine ⟨div_pos (mul_pos ha hδ) hD, ?_, ?_⟩
  · apply (div_lt_iff₀ hD).mpr
    have hh : δ < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh ha
  · rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hD).mpr
    have hh : 1 + a * M < 2 * (1 + a * M + δ) := by linarith
    exact mul_lt_mul_of_pos_left hh (mul_pos ha hδ)

theorem rayOracle_perturb_avoids_halfspace_boundary {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P)
    (ℓ : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ℓ p ≤ 1 - δ) (huBound : ℓ u ≤ M)
    (hs : 0 ≤ s) (hsε : s ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ℓ (oracle (p + s • u)) < 1 := by
  obtain ⟨hεpos, hεa, hεgap⟩ := facet_local_step_bounds ha hδ hM
  have hsa : s < a := hsε.trans_lt hεa
  have hr := perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs hsa hminus
  refine ⟨hr, ?_⟩
  obtain ⟨t, ht, heq, hupper⟩ :=
    rayOracle_perturb_scale_upper hconv hclosed hzero hp ha hs hsa hminus horacle
  have hgap : s * (1 + a * M) < a * δ :=
    (mul_le_mul_of_nonneg_right hsε (by positivity)).trans_lt hεgap
  have hbase : a * (1 - δ + s * M) < a - s := by
    nlinarith only [hgap]
  have hℓ : ℓ p + s * ℓ u ≤ 1 - δ + s * M :=
    add_le_add hpSlack (mul_le_mul_of_nonneg_left huBound hs)
  have hℓa : a * (ℓ p + s * ℓ u) < a - s :=
    (mul_le_mul_of_nonneg_left hℓ ha.le).trans_lt hbase
  have hscaled : a * (t * (ℓ p + s * ℓ u)) < a := by
    calc
      a * (t * (ℓ p + s * ℓ u)) = t * (a * (ℓ p + s * ℓ u)) := by ring
      _ < t * (a - s) := mul_lt_mul_of_pos_left hℓa ht
      _ ≤ a := hupper
  rw [heq, map_smul, map_add, map_smul]
  change t * (ℓ p + s * ℓ u) < 1
  nlinarith only [ha, hscaled]

theorem rayOracle_perturb_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M s : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hsε : |s| ≤ a * δ / (2 * (1 + a * M + δ)))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    p + s • u ≠ 0 ∧ ∀ j, L j (oracle (p + s • u)) < 1 := by
  have hsa : |s| < a := hsε.trans_lt (facet_local_step_bounds ha hδ hM).2.1
  by_cases hs : 0 ≤ s
  · have hsε' : s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (le_abs_self s).trans hsε
    refine ⟨perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp ha hs
      ((le_abs_self s).trans_lt hsa) hminus, ?_⟩
    intro j
    exact (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus (L j) (hpSlack j) ((le_abs_self _).trans (huBound j))
      hs hsε' horacle).2
  · have hs' : 0 ≤ -s := by linarith
    have hsε' : -s ≤ a * δ / (2 * (1 + a * M + δ)) :=
      (neg_le_abs s).trans hsε
    have hsa' : -s < a := (neg_le_abs s).trans_lt hsa
    have hminus' : (-a) • (-u) ∈ P := by
      simpa only [smul_neg, neg_smul, neg_neg] using hplus
    have heq : p + (-s) • (-u) = p + s • u := by
      simp only [smul_neg, neg_smul, neg_neg]
    refine ⟨heq ▸ perturb_frontier_ne_zero_of_negative_mem hconv hclosed hzero hp
      ha hs' hsa' hminus', ?_⟩
    intro j
    have huBound' : L j (-u) ≤ M := by
      rw [map_neg]
      exact (neg_le_abs _).trans (huBound j)
    have h := (rayOracle_perturb_avoids_halfspace_boundary hconv hclosed hzero hp
      ha hδ hM hminus' (L j) (hpSlack j) huBound' hs' hsε' horacle).2
    simpa only [heq] using h

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_pos_smul_eq {d : ℕ} {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {x : Fin d → ℝ} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    oracle (c • x) = oracle x := by
  have hcx : c • x ≠ 0 := smul_ne_zero hc.ne' hx
  obtain ⟨hq, t, ht, hqt⟩ := horacle (c • x) hcx
  obtain ⟨hp, s, hs, hps⟩ := horacle x hx
  apply frontier_eq_of_pos_smul hconv hclosed hzero hp hq (div_pos (mul_pos ht hc) hs)
  rw [hqt, hps, smul_smul, smul_smul, div_mul_cancel₀ _ hs.ne']

theorem facet_local_step_lt_half {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M) :
    a * δ / (2 * (1 + a * M + δ)) < a / 2 := by
  have hden : 0 < 2 * (1 + a * M + δ) := by positivity
  apply (div_lt_iff₀ hden).mpr
  have hm : 0 ≤ a * M := mul_nonneg ha.le hM
  have hh : δ < 1 + a * M + δ := by linarith
  have hk := mul_lt_mul_of_pos_left hh ha
  nlinarith only [hk]

theorem scaled_planar_first_two_queries_avoid_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    p - ε • u ≠ 0 ∧
    ∃ τ : ℝ, 0 < τ ∧ τ < 2 ∧
      oracle (p - ε • u) = τ • (p - ε • u) ∧
      (∀ j, L j (oracle (p - ε • u)) < 1) ∧
      let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
      r₂ ≠ 0 ∧ (∀ j, L j (oracle r₂) < 1) := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hεhalf : ε < a / 2 := facet_local_step_lt_half ha hδ hM
  have hfirst := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := -ε) (by rw [abs_neg, abs_of_pos hε]) horacle
  have heq₁ : p + (-ε) • u = p - ε • u := by simp only [neg_smul, sub_eq_add_neg]
  rw [heq₁] at hfirst
  refine ⟨hfirst.1, ?_⟩
  obtain ⟨hq, τ, hτ, hreply⟩ := horacle (p - ε • u) hfirst.1
  have hminus' : (-a) • (-u) ∈ P := by simpa only [smul_neg, neg_smul, neg_neg] using hplus
  have hεa : ε < a := (facet_local_step_bounds ha hδ hM).2.1
  obtain ⟨t, ht, hteq, hupper⟩ := rayOracle_perturb_scale_upper hconv hclosed hzero hp
    ha hε.le hεa hminus' horacle
  have heq₂ : p + ε • (-u) = p - ε • u := by simp only [smul_neg, sub_eq_add_neg]
  rw [heq₂] at hteq
  have htτ : t = τ := by
    apply (smul_left_injective ℝ hfirst.1)
    exact hteq.symm.trans hreply
  rw [htτ] at hupper
  have hτtwo : τ < 2 := by
    have hm := mul_lt_mul_of_pos_left hεhalf hτ
    nlinarith only [hupper, hm, ha]
  refine ⟨τ, hτ, hτtwo, hreply, hfirst.2, ?_⟩
  let s₂ := τ * ε / 2
  have hs₂ : 0 ≤ s₂ := by dsimp [s₂]; positivity
  have hs₂ε : s₂ ≤ ε := by
    dsimp only [s₂]
    have hm := mul_lt_mul_of_pos_right hτtwo hε
    linarith
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound
    (s := s₂) (by rw [abs_of_nonneg hs₂]; exact hs₂ε) horacle
  have hc : 0 < 2 / (1 + τ) := by positivity
  have hr₂ : (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p =
      (2 / (1 + τ)) • (p + s₂ • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [s₂]
    ring
  rw [hr₂]
  refine ⟨smul_ne_zero hc.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hc]
  exact hsafe.2

end Grunbaum2003

namespace Grunbaum2003

theorem rayOracle_local_cone_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    α • p + β • u ≠ 0 ∧ ∀ j, L j (oracle (α • p + β • u)) < 1 := by
  have hs : |β / α| ≤ a * δ / (2 * (1 + a * M + δ)) := by
    rw [abs_div, abs_of_pos hα]
    apply (div_le_iff₀ hα).mpr
    simpa only [mul_comm] using hβ
  have hsafe := rayOracle_perturb_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hs horacle
  have heq : α • p + β • u = α • (p + (β / α) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [heq]
  refine ⟨smul_ne_zero hα.ne' hsafe.1, ?_⟩
  rw [rayOracle_pos_smul_eq hconv hclosed hzero horacle hsafe.1 hα]
  exact hsafe.2

theorem local_cone_convex_coefficients {α β γ η ε θ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * ε) (hη : |η| ≤ γ * ε)
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    0 < (1 - θ) * α + θ * γ ∧
      |(1 - θ) * β + θ * η| ≤ ((1 - θ) * α + θ * γ) * ε := by
  have hcomp : 0 ≤ 1 - θ := sub_nonneg.mpr hθone
  constructor
  · by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hα
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hcomp hα.le)
        (mul_pos (lt_of_le_of_ne hθ (Ne.symm hz)) hγ)
  · calc
      |(1 - θ) * β + θ * η| ≤ |(1 - θ) * β| + |θ * η| := abs_add_le _ _
      _ = (1 - θ) * |β| + θ * |η| := by
        rw [abs_mul, abs_of_nonneg hcomp, abs_mul, abs_of_nonneg hθ]
      _ ≤ (1 - θ) * (α * ε) + θ * (γ * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left hβ hcomp)
          (mul_le_mul_of_nonneg_left hη hθ)
      _ = ((1 - θ) * α + θ * γ) * ε := by ring

theorem rayOracle_safe_reference_segment {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M α β γ η θ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hα : 0 < α) (hγ : 0 < γ)
    (hβ : |β| ≤ α * (a * δ / (2 * (1 + a * M + δ))))
    (hη : |η| ≤ γ * (a * δ / (2 * (1 + a * M + δ))))
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let r := (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  obtain ⟨hpos, hbound⟩ := local_cone_convex_coefficients hα hγ hβ hη hθ hθone
  have hsafe := rayOracle_local_cone_avoids_known_facets hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound hpos hbound horacle
  have heq : (1 - θ) • (α • p + β • u) + θ • (γ • p + η • u) =
      ((1 - θ) * α + θ * γ) • p + ((1 - θ) * β + θ * η) • u := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [heq] using hsafe

end Grunbaum2003

namespace Grunbaum2003.RayPlanar

theorem convex_secant_zero_progress {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x) :
    0 < h y - h x ∧
      0 ≤ (x * h y - y * h x) / (h y - h x) ∧
      (x * h y - y * h x) / (h y - h x) < x := by
  have hcross := hconv.secant_mono_aux1 (Set.mem_univ 0) (Set.mem_univ y) hx hxy
  simp only [sub_zero, hzero, mul_zero, zero_add] at hcross
  have hprod : 0 < (y - x) * h x := mul_pos (sub_pos.mpr hxy) hhx
  have hden : 0 < h y - h x := by
    by_contra hn
    have hle : h y ≤ h x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle hx.le
    nlinarith only [hcross, hprod, hmul]
  refine ⟨hden, div_nonneg (by linarith only [hcross]) hden.le, ?_⟩
  apply (div_lt_iff₀ hden).mpr
  nlinarith only [hprod]

theorem secant_zero_of_common_affine_piece {h : ℝ → ℝ} {x y a b : ℝ}
    (hden : h y - h x ≠ 0)
    (hx : h x = a * x + b) (hy : h y = a * y + b) :
    a * ((x * h y - y * h x) / (h y - h x)) + b = 0 := by
  have hz : ((x * h y - y * h x) / (h y - h x)) * (h y - h x) =
      x * h y - y * h x := div_mul_cancel₀ _ hden
  have hp : (a * ((x * h y - y * h x) / (h y - h x)) + b) *
      (h y - h x) = 0 := by
    calc
      _ = a * (((x * h y - y * h x) / (h y - h x)) * (h y - h x)) +
          b * (h y - h x) := by ring
      _ = a * (x * h y - y * h x) + b * (h y - h x) := by rw [hz]
      _ = 0 := by rw [hx, hy]; ring
  exact (mul_eq_zero.mp hp).resolve_right hden

theorem convex_affine_piece_active_between {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) {a b x z y : ℝ}
    (hmajor : ∀ t, a * t + b ≤ h t)
    (hx : h x = a * x + b) (hy : h y = a * y + b)
    (hxz : x ≤ z) (hzy : z ≤ y) : h z = a * z + b := by
  rcases eq_or_lt_of_le hxz with rfl | hxz
  · exact hx
  rcases eq_or_lt_of_le hzy with rfl | hzy
  · exact hy
  apply le_antisymm ?_ (hmajor z)
  have hk := hconv.secant_mono_aux1 (Set.mem_univ x) (Set.mem_univ y) hxz hzy
  rw [hx, hy] at hk
  by_contra hn
  have hp : 0 < (y - x) * (h z - (a * z + b)) :=
    mul_pos (sub_pos.mpr (hxz.trans hzy)) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem third_secant_response_leaves_common_piece {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {x y a b : ℝ} (hx : 0 < x) (hxy : x < y) (hhx : 0 < h x)
    (hax : h x = a * x + b) (hay : h y = a * y + b)
    (hnext : 0 < h ((x * h y - y * h x) / (h y - h x))) :
    h ((x * h y - y * h x) / (h y - h x)) ≠
      a * ((x * h y - y * h x) / (h y - h x)) + b := by
  have hden := (convex_secant_zero_progress hconv hzero hx hxy hhx).1
  have hz := secant_zero_of_common_affine_piece hden.ne' hax hay
  rw [hz]
  exact ne_of_gt hnext

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem secant_active_piece_indices_close {n m : ℕ} {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    (a b : Fin m → ℝ) (hmajor : ∀ j t, a j * t + b j ≤ h t)
    (x : Fin n → ℝ) (hx : StrictAnti x) (hpositive : ∀ i, 0 < x i)
    (hgap : ∀ i, 0 < h (x i))
    (piece : Fin n → Fin m) (hactive : ∀ i, h (x i) = a (piece i) * x i + b (piece i))
    (hrec : ∀ i : ℕ, ∀ hi : i + 2 < n,
      x ⟨i + 2, hi⟩ =
        (x ⟨i + 1, by omega⟩ * h (x ⟨i, by omega⟩) -
          x ⟨i, by omega⟩ * h (x ⟨i + 1, by omega⟩)) /
        (h (x ⟨i, by omega⟩) - h (x ⟨i + 1, by omega⟩)))
    {i j : Fin n} (hij : i.val + 2 ≤ j.val) : piece i ≠ piece j := by
  intro heq
  have hi2 : i.val + 2 < n := lt_of_le_of_lt hij j.isLt
  let i₁ : Fin n := ⟨i.val + 1, by omega⟩
  let i₂ : Fin n := ⟨i.val + 2, hi2⟩
  have hx₁ : x i₁ < x i := hx (by change i.val < i.val + 1; omega)
  have hx₂ : x i₂ < x i₁ := hx (by change i.val + 1 < i.val + 2; omega)
  have hxj₁ : x j ≤ x i₁ := (hx.antitone (by change i.val + 1 ≤ j.val; omega))
  have hxj₂ : x j ≤ x i₂ := (hx.antitone (by exact hij))
  have haj : h (x j) = a (piece i) * x j + b (piece i) := by rw [heq]; exact hactive j
  have ha₁ : h (x i₁) = a (piece i) * x i₁ + b (piece i) :=
    convex_affine_piece_active_between hconv (hmajor (piece i)) haj (hactive i)
      hxj₁ hx₁.le
  have ha₂ : h (x i₂) = a (piece i) * x i₂ + b (piece i) :=
    convex_affine_piece_active_between hconv (hmajor (piece i)) haj (hactive i)
      hxj₂ (hx₂.trans hx₁).le
  have hr : x i₂ = (x i₁ * h (x i) - x i * h (x i₁)) / (h (x i) - h (x i₁)) :=
    hrec i.val hi2
  have hnext : 0 < h ((x i₁ * h (x i) - x i * h (x i₁)) / (h (x i) - h (x i₁))) := by
    rw [← hr]
    exact hgap i₂
  have hne := third_secant_response_leaves_common_piece hconv hzero
    (hpositive i₁) hx₁ (hgap i₁) ha₁ (hactive i) hnext
  rw [← hr] at hne
  exact hne ha₂

theorem secant_nonterminal_query_count_le_twice {n m : ℕ} {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    (a b : Fin m → ℝ) (hmajor : ∀ j t, a j * t + b j ≤ h t)
    (x : Fin n → ℝ) (hx : StrictAnti x) (hpositive : ∀ i, 0 < x i)
    (hgap : ∀ i, 0 < h (x i))
    (piece : Fin n → Fin m) (hactive : ∀ i, h (x i) = a (piece i) * x i + b (piece i))
    (hrec : ∀ i : ℕ, ∀ hi : i + 2 < n,
      x ⟨i + 2, hi⟩ =
        (x ⟨i + 1, by omega⟩ * h (x ⟨i, by omega⟩) -
          x ⟨i, by omega⟩ * h (x ⟨i + 1, by omega⟩)) /
        (h (x ⟨i, by omega⟩) - h (x ⟨i + 1, by omega⟩))) : n ≤ 2 * m := by
  let f : Fin n → Fin m × Fin 2 := fun i => (piece i, ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)
  have hf : Function.Injective f := by
    intro i j heq
    have hp : piece i = piece j := congrArg Prod.fst heq
    have hmod : i.val % 2 = j.val % 2 := congrArg (fun z : Fin m × Fin 2 => z.2.val) heq
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hsep : i.val + 2 ≤ j.val := by omega
      exact secant_active_piece_indices_close hconv hzero a b hmajor x hx hpositive hgap
        piece hactive hrec hsep hp
    · have hsep : j.val + 2 ≤ i.val := by omega
      exact secant_active_piece_indices_close hconv hzero a b hmajor x hx hpositive hgap
        piece hactive hrec hsep hp.symm
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm m 2] using hc

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem label_parity_injective {n u : ℕ} (piece : Fin n → Fin u)
    (hclose : ∀ i j : Fin n, i.val + 2 ≤ j.val → piece i ≠ piece j) :
    Function.Injective (fun i : Fin n =>
      (piece i, (⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2))) := by
  intro i j heq
  have hp : piece i = piece j := congrArg Prod.fst heq
  have hmod : i.val % 2 = j.val % 2 := congrArg (fun z : Fin u × Fin 2 => z.2.val) heq
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hclose i j (by omega) hp
  · exact hclose j i (by omega) hp.symm

theorem two_side_query_count_of_close_disjoint_labels {n m u : ℕ}
    (positive : Fin n → Fin u) (negative : Fin m → Fin u)
    (hpos : ∀ i j : Fin n, i.val + 2 ≤ j.val → positive i ≠ positive j)
    (hneg : ∀ i j : Fin m, i.val + 2 ≤ j.val → negative i ≠ negative j)
    (hdisjoint : ∀ i j, positive i ≠ negative j) : n + m ≤ 2 * u := by
  let fp : Fin n → Fin u × Fin 2 := fun i =>
    (positive i, ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)
  let fn : Fin m → Fin u × Fin 2 := fun i =>
    (negative i, ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)
  let f : Fin n ⊕ Fin m → Fin u × Fin 2 := Sum.elim fp fn
  have hfp : Function.Injective fp := label_parity_injective positive hpos
  have hfn : Function.Injective fn := label_parity_injective negative hneg
  have hf : Function.Injective f := by
    intro i j heq
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hfp heq)
      | inr j => exact False.elim (hdisjoint i j (congrArg Prod.fst heq))
    | inr i =>
      cases j with
      | inl j => exact False.elim (hdisjoint j i (congrArg Prod.fst heq).symm)
      | inr j => exact congrArg Sum.inr (hfn heq)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Nat.mul_comm u 2] using hc

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def finiteAffineEnvelope {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => a j * x + b j)

lemma finiteAffineEnvelope_major {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (j : Fin m) (x : ℝ) : a j * x + b j ≤ finiteAffineEnvelope hm a b x :=
  Finset.le_sup' (fun k => a k * x + b k) (Finset.mem_univ j)

lemma finiteAffineEnvelope_attained {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ)
    (x : ℝ) : ∃ j, finiteAffineEnvelope hm a b x = a j * x + b j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin m))) ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun j => a j * x + b j)
  exact ⟨j, hj⟩

lemma finiteAffineEnvelope_convex {m : ℕ} (hm : 0 < m) (a b : Fin m → ℝ) :
    ConvexOn ℝ Set.univ (finiteAffineEnvelope hm a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hab
  simp only [smul_eq_mul]
  apply Finset.sup'_le
  intro j _
  have hx := finiteAffineEnvelope_major hm a b j x
  have hy := finiteAffineEnvelope_major hm a b j y
  calc
    a j * (α * x + β * y) + b j =
        α * (a j * x + b j) + β * (a j * y + b j) := by
      linear_combination -b j * hab
    _ ≤ α * finiteAffineEnvelope hm a b x + β * finiteAffineEnvelope hm a b y :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)

theorem frontier_finite_halfspaces_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {q : Fin d → ℝ} (hq : q ∈ frontier P) :
    (∀ j, L j q ≤ 1) ∧ ∃ j, L j q = 1 := by
  have hclosed : IsClosed P := by
    rw [hP, Set.ofPred_forall]
    exact isClosed_iInter (fun j => isClosed_le (L j).continuous continuous_const)
  have hle : ∀ j, L j q ≤ 1 := by
    have hmem := hclosed.frontier_subset hq
    rwa [hP] at hmem
  refine ⟨hle, ?_⟩
  by_contra hn
  have hlt : ∀ j, L j q < 1 := by
    intro j
    exact lt_of_le_of_ne (hle j) (by intro heq; exact hn ⟨j, heq⟩)
  have hopen : IsOpen {x : Fin d → ℝ | ∀ j, L j x < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (L j).continuous continuous_const)
  have hsub : {x : Fin d → ℝ | ∀ j, L j x < 1} ⊆ P := by
    intro x hx
    rw [hP]
    exact fun j => (hx j).le
  exact hq.2 (interior_maximal hsub hopen hlt)

theorem rayOracle_halfspace_envelope_eq {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ oracle (p + x • u) = t • (p + x • u) ∧
      finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 1 / t - 1 := by
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + x • u) hr
  obtain ⟨hineq, j, hj⟩ := frontier_finite_halfspaces_active L hP hq
  refine ⟨t, ht, heq, le_antisymm ?_ ?_⟩
  · apply Finset.sup'_le
    intro k _
    have hk := hineq k
    rw [heq, map_smul, map_add, map_smul] at hk
    change t * (L k p + x * L k u) ≤ 1 at hk
    have hdiv : L k p + x * L k u ≤ 1 / t := (le_div_iff₀ ht).mpr (by nlinarith only [hk])
    linarith only [hdiv]
  · have hj' := hj
    rw [heq, map_smul, map_add, map_smul] at hj'
    change t * (L j p + x * L j u) = 1 at hj'
    have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj'])
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hdiv, hmajor]

theorem halfspace_envelope_zero_at_boundary {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (hp : p ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) 0 = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    dsimp only
    simp only [mul_zero, zero_add]
    linarith only [hle k]
  · have h := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j 0
    simpa only [mul_zero, zero_add, hj, sub_self] using h

theorem convex_gap_nonneg_positive_of_negative_zero {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {z x : ℝ} (hz : z < 0) (hzval : h z = 0) (hx : 0 ≤ x) : 0 ≤ h x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa only [hzero] using (le_refl (0 : ℝ))
  have hk := hconv.secant_mono_aux1 (Set.mem_univ z) (Set.mem_univ x) hz hx
  rw [hzero, hzval] at hk
  simp only [mul_zero, add_zero, zero_add, zero_sub] at hk
  by_contra hn
  have hp : 0 < (-z) * (-h x) := mul_pos (neg_pos.mpr hz) (neg_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hk, hp]

theorem rayOracle_active_halfspace_envelope {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0)
    (j : Fin m) (hj : L j (oracle (p + x • u)) = 1) :
    finiteAffineEnvelope hm (fun k => L k u) (fun k => L k p - 1) x =
      L j u * x + (L j p - 1) := by
  obtain ⟨t, ht, heq, henv⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p u x hr
  rw [heq, map_smul, map_add, map_smul] at hj
  change t * (L j p + x * L j u) = 1 at hj
  have hdiv : L j p + x * L j u = 1 / t := (eq_div_iff ht.ne').mpr (by nlinarith only [hj])
  linarith only [henv, hdiv]

theorem rayOracle_common_halfspace_opposite_sides_incident {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {x y : ℝ} (hx : x < 0) (hy : 0 < y)
    (hrx : p + x • u ≠ 0) (hry : p + y • u ≠ 0)
    (j : Fin m)
    (hjx : L j (oracle (p + x • u)) = 1)
    (hjy : L j (oracle (p + y • u)) = 1) : L j p = 1 := by
  have hax := rayOracle_active_halfspace_envelope hm L hP horacle p u x hrx j hjx
  have hay := rayOracle_active_halfspace_envelope hm L hP horacle p u y hry j hjy
  have hconv := finiteAffineEnvelope_convex hm (fun k => L k u) (fun k => L k p - 1)
  have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j
  have hact := convex_affine_piece_active_between hconv hmajor hax hay hx.le hy.le
  rw [halfspace_envelope_zero_at_boundary hm L hP p u hp] at hact
  simp only [mul_zero, zero_add] at hact
  linarith only [hact]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem envelope_zero_at_frontier {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    (p u : Fin d → ℝ) (x : ℝ) (hp : p + x • u ∈ frontier P) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 0 := by
  obtain ⟨hle, j, hj⟩ := frontier_finite_halfspaces_active L hP hp
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    have hk := hle k
    rw [map_add, map_smul] at hk
    change L k p + x * L k u ≤ 1 at hk
    linarith only [hk]
  · have hj' := hj
    rw [map_add, map_smul] at hj'
    change L j p + x * L j u = 1 at hj'
    have hmajor := finiteAffineEnvelope_major hm (fun k => L k u) (fun k => L k p - 1) j x
    linarith only [hmajor, hj']

theorem first_reference_chord_data {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {x | ∀ j, L j x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (hp : p ∈ frontier P)
    {ε τ : ℝ} (hτ : 0 < τ) (hr : p - ε • u ≠ 0)
    (hreply : oracle (p - ε • u) = τ • (p - ε • u)) :
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let B := r₂ - p
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
    H 0 = 0 ∧ H (-(1 + τ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → 0 ≤ H x) ∧
      oracle (p - ε • u) = p + (-(1 + τ)) • B ∧
      (1 / 2 : ℝ) • (p + r₂) = p + (1 / 2 : ℝ) • B := by
  dsimp only
  let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
  let B := r₂ - p
  have hden : 1 + τ ≠ 0 := ne_of_gt (by linarith)
  have hanchor : p + (-(1 + τ)) • B = τ • (p - ε • u) := by
    ext j
    dsimp [B, r₂]
    field_simp
    <;> ring
  have hp₁ : p + (-(1 + τ)) • B ∈ frontier P := by
    rw [hanchor, ← hreply]
    exact (horacle (p - ε • u) hr).1
  have hzero := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hnegative := envelope_zero_at_frontier hm L hP p B (-(1 + τ)) hp₁
  refine ⟨hzero, hnegative, ?_, hreply.trans hanchor.symm, ?_⟩
  · intro x hx
    exact convex_gap_nonneg_positive_of_negative_zero
      (finiteAffineEnvelope_convex hm _ _) hzero (by linarith) hnegative hx
  · ext j
    dsimp [B]
    ring

theorem first_reference_segment_avoids_known_facets {d : ℕ} {ι : Type*}
    {P : Set (Fin d → ℝ)}
    (hconv : Convex ℝ P) (hclosed : IsClosed P)
    (hzero : (0 : Fin d → ℝ) ∈ interior P)
    {p u : Fin d → ℝ} (hp : p ∈ frontier P)
    {a δ M τ x : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hminus : (-a) • u ∈ P) (hplus : a • u ∈ P)
    (L : ι → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hpSlack : ∀ j, L j p ≤ 1 - δ) (huBound : ∀ j, |L j u| ≤ M)
    (hτ : 0 < τ) (hτtwo : τ ≤ 2) (hx : 0 ≤ x) (hxone : x ≤ 1)
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle) :
    let ε := a * δ / (2 * (1 + a * M + δ))
    let r₂ := (τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p
    let r := p + x • (r₂ - p)
    r ≠ 0 ∧ ∀ j, L j (oracle r) < 1 := by
  dsimp only
  let ε := a * δ / (2 * (1 + a * M + δ))
  have hε : 0 < ε := (facet_local_step_bounds ha hδ hM).1
  have hden : 0 < 1 + τ := by linarith
  have hc : 0 < 2 / (1 + τ) := div_pos (by norm_num) hden
  have hβ : |(0 : ℝ)| ≤ 1 * ε := by simpa only [abs_zero, one_mul] using hε.le
  have hη : |τ * ε / (1 + τ)| ≤ (2 / (1 + τ)) * ε := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hτ.le hε.le) hden.le)]
    have hm := mul_le_mul_of_nonneg_right hτtwo (div_nonneg hε.le hden.le)
    calc
      τ * ε / (1 + τ) = τ * (ε / (1 + τ)) := by ring
      _ ≤ 2 * (ε / (1 + τ)) := hm
      _ = (2 / (1 + τ)) * ε := by ring
  have hsafe := rayOracle_safe_reference_segment hconv hclosed hzero hp
    ha hδ hM hminus hplus L hpSlack huBound (by norm_num : (0 : ℝ) < 1)
    hc hβ hη hx hxone horacle
  have heq : p + x • ((τ / (1 + τ)) • (ε • u) + (2 / (1 + τ)) • p - p) =
      (1 - x) • ((1 : ℝ) • p + (0 : ℝ) • u) +
        x • ((2 / (1 + τ)) • p + (τ * ε / (1 + τ)) • u) := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [← heq] at hsafe
  exact hsafe

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem halfspace_common_active_of_positive_combo {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {x y q : Fin d → ℝ} (hx : x ∈ P) (hy : y ∈ P) (hq : q ∈ frontier P)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hab : α + β = 1)
    (heq : q = α • x + β • y) :
    ∃ j : Fin m, L j x = 1 ∧ L j y = 1 ∧ L j q = 1 := by
  obtain ⟨_, j, hj⟩ := frontier_finite_halfspaces_active L hP hq
  have hxj : L j x ≤ 1 := by rw [hP] at hx; exact hx j
  have hyj : L j y ≤ 1 := by rw [hP] at hy; exact hy j
  have hm := hj
  rw [heq, map_add, map_smul, map_smul] at hm
  change α * L j x + β * L j y = 1 at hm
  have hA : 0 ≤ α * (1 - L j x) := mul_nonneg hα.le (sub_nonneg.mpr hxj)
  have hB : 0 ≤ β * (1 - L j y) := mul_nonneg hβ.le (sub_nonneg.mpr hyj)
  have hsum : α * (1 - L j x) + β * (1 - L j y) = 0 := by nlinarith only [hm, hab]
  have hAzero : α * (1 - L j x) = 0 := le_antisymm (by linarith only [hsum, hB]) hA
  have hBzero : β * (1 - L j y) = 0 := le_antisymm (by linarith only [hsum, hA]) hB
  have hxval : 1 - L j x = 0 := (mul_eq_zero.mp hAzero).resolve_left hα.ne'
  have hyval : 1 - L j y = 0 := (mul_eq_zero.mp hBzero).resolve_left hβ.ne'
  refine ⟨j, ?_, ?_, hj⟩ <;> linarith only [hxval, hyval]

theorem secant_zero_replies_bracket {d : ℕ} (p u : Fin d → ℝ)
    {x y gx gy : ℝ} (hx : 0 < x) (hxy : x < y)
    (hgx : 0 < gx) (hgy : 0 < gy)
    (hzero : x * (gy - 1) = y * (gx - 1)) :
    let θ := x * gy / (y * gx)
    0 < θ ∧ θ < 1 ∧
      (1 / gx) • (p + x • u) =
        (1 - θ) • p + θ • ((1 / gy) • (p + y • u)) := by
  have hy : 0 < y := hx.trans hxy
  have hden : 0 < y * gx := mul_pos hy hgx
  dsimp only
  refine ⟨div_pos (mul_pos hx hgy) hden, ?_, ?_⟩
  · apply (div_lt_one hden).mpr
    nlinarith only [hzero, hxy]
  · ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination p j * hzero

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem rayOracle_halfspace_envelope_zero_iff_fixed {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0) :
    finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 0 ↔
      oracle (p + x • u) = p + x • u := by
  obtain ⟨t, ht, heq, henv⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p u x hr
  constructor
  · intro hz
    have hdiv : 1 / t = 1 := by linarith only [hz, henv]
    have htone : t = 1 := by
      have hmul := (div_eq_iff ht.ne').mp hdiv
      linarith only [hmul]
    rw [heq, htone, one_smul]
  · intro hfix
    have hscale : t • (p + x • u) = (1 : ℝ) • (p + x • u) := by
      rw [← heq, hfix, one_smul]
    have htone : t = 1 := (smul_left_injective ℝ hr) hscale
    simpa only [htone, div_one, sub_self] using henv

theorem rayOracle_reference_level_iff_envelope_zero {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSu : S u = 0) :
    p + x • u ≠ 0 ∧
      (S (oracle (p + x • u)) = 1 ↔
        finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x = 0) := by
  have hSinput : S (p + x • u) = 1 := by
    rw [map_add, map_smul, hSp, hSu]
    simp only [smul_eq_mul, mul_zero, add_zero]
  have hr : p + x • u ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hSinput
    norm_num at hSinput
  refine ⟨hr, ?_⟩
  rw [rayOracle_halfspace_envelope_zero_iff_fixed hm L hP horacle p u x hr]
  obtain ⟨hq, t, ht, heq⟩ := horacle (p + x • u) hr
  constructor
  · intro hlevel
    rw [heq, map_smul, hSinput] at hlevel
    change t * 1 = 1 at hlevel
    have htone : t = 1 := by simpa only [mul_one] using hlevel
    rw [heq, htone, one_smul]
  · intro hfix
    rw [hfix]
    exact hSinput

theorem rayOracle_nonnegative_envelope_pos_iff_nonfixed {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p u : Fin d → ℝ) (x : ℝ) (hr : p + x • u ≠ 0)
    (hnonneg : 0 ≤ finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x) :
    0 < finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x ↔
      oracle (p + x • u) ≠ p + x • u := by
  have hiff := rayOracle_halfspace_envelope_zero_iff_fixed hm L hP horacle p u x hr
  constructor
  · intro hpos hfix
    exact hpos.ne' (hiff.mpr hfix)
  · intro hnonfix
    have hne : finiteAffineEnvelope hm (fun j => L j u) (fun j => L j p - 1) x ≠ 0 := by
      intro hz
      exact hnonfix (hiff.mp hz)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem reference_chord_reply_gap_positive {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hgap : 0 < finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x) :
    ∃ tx ty : ℝ, 0 < ty ∧ ty < tx ∧
      oracle (p + x • B) = tx • (p + x • B) ∧
      oracle (p + y • B) = ty • (p + y • B) ∧
      0 < S (oracle (p + x • B) - oracle (p + y • B)) := by
  have hrx := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B x S hSp hSB).1
  have hry := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B y S hSp hSB).1
  obtain ⟨tx, htx, heqx, hHx⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p B x hrx
  obtain ⟨ty, hty, heqy, hHy⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p B y hry
  have hconv := finiteAffineEnvelope_convex hm (fun j => L j B) (fun j => L j p - 1)
  have hzero := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hdiff := (convex_secant_zero_progress hconv hzero hx hxy hgap).1
  rw [hHx, hHy] at hdiff
  have hrecip : 1 / tx < 1 / ty := by linarith only [hdiff]
  have hscale : ty < tx := (one_div_lt_one_div htx hty).mp hrecip
  refine ⟨tx, ty, hty, hscale, heqx, heqy, ?_⟩
  rw [map_sub, heqx, heqy, map_smul, map_smul, map_add, map_add, map_smul, map_smul, hSp, hSB]
  change 0 < tx * (1 + x * 0) - ty * (1 + y * 0)
  simpa only [mul_zero, add_zero, mul_one] using sub_pos.mpr hscale

theorem reply_chord_secant_intersection {d : ℕ} (p B : Fin d → ℝ)
    {x y tx ty : ℝ} (hty : 0 < ty) (hscale : ty < tx) :
    let qx := tx • (p + x • B)
    let qy := ty • (p + y • B)
    let z := (x * (1 / ty - 1) - y * (1 / tx - 1)) / ((1 / ty - 1) - (1 / tx - 1))
    qy + ((1 - ty) / (tx - ty)) • (qx - qy) = p + z • B := by
  have htx : 0 < tx := hty.trans hscale
  have hden : tx - ty ≠ 0 := (sub_pos.mpr hscale).ne'
  have hden' : -ty + tx ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using hden
  have hrecip : (1 / ty - 1) - (1 / tx - 1) ≠ 0 := by
    have hh := one_div_lt_one_div_of_lt hty hscale
    linarith only [hh]
  dsimp only
  ext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [htx.ne', hty.ne', hden, hden', hrecip]
  ring_nf
  field_simp [hden'] <;> ring

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem firstIntersectionDirection_reference_value (t : ℝ) (previous current : Fin 2 → ℝ)
    (hden : firstChordValue t (current - previous) ≠ 0) :
    firstChordValue t (firstIntersectionDirection t previous current) = t := by
  let δ := firstChordValue t (current - previous)
  let a := firstChordValue t previous
  let s := firstIntersectionParameter t previous current
  have hm : s * δ = t - a := div_mul_cancel₀ _ hden
  change (t - 1) * (previous 0 + s * (current 0 - previous 0)) +
    t * (previous 1 + s * (current 1 - previous 1)) = t
  dsimp [δ, a, firstChordValue] at hm
  nlinarith only [hm]

theorem reference_value_anchor_iff_first_coordinate_zero {t : ℝ} (ht : 0 < t)
    (r : Fin 2 → ℝ) (hvalue : firstChordValue t r = t) :
    r 0 = 0 ↔ r = suppliedPoint := by
  constructor
  · intro hr₀
    have hr₁ : r 1 = 1 := by
      change (t - 1) * r 0 + t * r 1 = t at hvalue
      rw [hr₀, mul_zero, zero_add] at hvalue
      exact mul_left_cancel₀ ht.ne' (by simpa only [mul_one] using hvalue)
    funext i
    fin_cases i
    · change r 0 = 0
      exact hr₀
    · change r 1 = 1
      exact hr₁
  · intro hr
    rw [hr]
    rfl

theorem firstIntersectionDirection_anchor_iff {t : ℝ} (ht : 0 < t)
    (previous current : Fin 2 → ℝ)
    (hden : firstChordValue t (current - previous) ≠ 0) :
    firstIntersectionDirection t previous current 0 = 0 ↔
      firstIntersectionDirection t previous current = suppliedPoint :=
  reference_value_anchor_iff_first_coordinate_zero ht _
    (firstIntersectionDirection_reference_value t previous current hden)

theorem firstChord_test_zero_iff_current_on_reference (t : ℝ)
    (previous current : Fin 2 → ℝ) :
    firstChordValue t previous + firstChordValue t (current - previous) - t = 0 ↔
      firstChordValue t current = t := by
  have heq : firstChordValue t previous + firstChordValue t (current - previous) - t =
      firstChordValue t current - t := by
    dsimp only [firstChordValue]
    simp only [Pi.sub_apply]
    ring
  rw [heq, sub_eq_zero]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem reference_reply_gap_of_envelope_gap {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (x y : ℝ)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    (hgap : finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x <
      finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y) :
    ∃ tx ty : ℝ, 0 < ty ∧ ty < tx ∧
      oracle (p + x • B) = tx • (p + x • B) ∧
      oracle (p + y • B) = ty • (p + y • B) ∧
      finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x = 1 / tx - 1 ∧
      finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y = 1 / ty - 1 ∧
      S (oracle (p + x • B) - oracle (p + y • B)) = tx - ty := by
  have hrx := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B x S hSp hSB).1
  have hry := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B y S hSp hSB).1
  obtain ⟨tx, htx, heqx, hHx⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p B x hrx
  obtain ⟨ty, hty, heqy, hHy⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle p B y hry
  have hrecip : 1 / tx < 1 / ty := by linarith only [hgap, hHx, hHy]
  have hscale : ty < tx := (one_div_lt_one_div htx hty).mp hrecip
  refine ⟨tx, ty, hty, hscale, heqx, heqy, hHx, hHy, ?_⟩
  rw [map_sub, heqx, heqy, map_smul, map_smul, map_add, map_add, map_smul, map_smul, hSp, hSB]
  change tx * (1 + x * 0) - ty * (1 + y * 0) = tx - ty
  ring

theorem convex_gap_strictly_smaller_parameter {h : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0)
    {z x : ℝ} (hz : 0 < z) (hzx : z < x) (hxval : 0 < h x) : h z < h x := by
  have hk := hconv.secant_mono_aux1 (Set.mem_univ 0) (Set.mem_univ x) hz hzx
  simp only [sub_zero, hzero, mul_zero, zero_add] at hk
  have hprod : 0 < (x - z) * h x := mul_pos (sub_pos.mpr hzx) hxval
  by_contra hn
  have hle : h x ≤ h z := le_of_not_gt hn
  have hmul := mul_le_mul_of_nonneg_left hle (hz.trans hzx).le
  nlinarith only [hk, hprod, hmul]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem rayOracle_reference_secant_step {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hcurrent : 0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x)
    (hprevious : 0 < finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y) :
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
    let current := oracle (p + x • B)
    let previous := oracle (p + y • B)
    let z := (x * H y - y * H x) / (H y - H x)
    0 < S (current - previous) ∧
      previous + ((1 - S previous) / S (current - previous)) • (current - previous) =
        p + z • B ∧
      p + z • B ≠ 0 ∧
      (S current = 1 ↔ H x = 0) ∧
      (S current ≠ 1 → 0 < H x) ∧
      (H x = 0 → z = x ∧ current = p + x • B) ∧
      (0 < H x → 0 ≤ z ∧ z < x ∧ (0 < z → H z < H x)) := by
  dsimp only
  let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
  let current := oracle (p + x • B)
  let previous := oracle (p + y • B)
  let z := (x * H y - y * H x) / (H y - H x)
  have hconv := finiteAffineEnvelope_convex hm (fun j => L j B) (fun j => L j p - 1)
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hgap : H x < H y :=
    convex_gap_strictly_smaller_parameter hconv hzero hx hxy hprevious
  obtain ⟨tx, ty, hty, hscale, heqx, heqy, hHx, hHy, hSdiff⟩ :=
    reference_reply_gap_of_envelope_gap hm L hP horacle p B x y S hSp hSB hgap
  have hSprevious : S previous = ty := by
    change S (oracle (p + y • B)) = ty
    rw [heqy, map_smul, map_add, map_smul, hSp, hSB]
    change ty * (1 + y * 0) = ty
    ring
  have hintersection : previous + ((1 - S previous) / S (current - previous)) •
      (current - previous) = p + z • B := by
    rw [hSprevious, hSdiff]
    change oracle (p + y • B) + ((1 - ty) / (tx - ty)) •
      (oracle (p + x • B) - oracle (p + y • B)) = p + z • B
    rw [heqx, heqy]
    dsimp only [z, H]
    rw [hHx, hHy]
    exact reply_chord_secant_intersection p B hty hscale
  have hlevel := rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B x S hSp hSB
  refine ⟨?_, hintersection, ?_, hlevel.2, ?_, ?_, ?_⟩
  · rw [hSdiff]
    exact sub_pos.mpr hscale
  · exact (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B z S hSp hSB).1
  · intro hnotlevel
    have hnotzero : H x ≠ 0 := fun hz => hnotlevel (hlevel.2.mpr hz)
    exact lt_of_le_of_ne hcurrent (Ne.symm hnotzero)
  · intro hz
    change H x = 0 at hz
    have hden : H y ≠ 0 := hprevious.ne'
    refine ⟨?_, ?_⟩
    · change (x * H y - y * H x) / (H y - H x) = x
      rw [hz, mul_zero, sub_zero, sub_zero, mul_div_cancel_right₀ x hden]
    · exact (rayOracle_halfspace_envelope_zero_iff_fixed hm L hP horacle p B x hlevel.1).mp hz
  · intro hpos
    obtain ⟨_, hznonneg, hzlt⟩ := convex_secant_zero_progress hconv hzero hx hxy hpos
    refine ⟨hznonneg, hzlt, ?_⟩
    intro hzpos
    exact convex_gap_strictly_smaller_parameter hconv hzero hzpos hzlt hpos

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def secantPairSequence (H : ℝ → ℝ) (y x : ℝ) : ℕ → ℝ × ℝ
  | 0 => (y, x)
  | n + 1 =>
    let v := secantPairSequence H y x n
    (v.2, (v.2 * H v.1 - v.1 * H v.2) / (H v.1 - H v.2))

def secantParameterSequence (H : ℝ → ℝ) (y x : ℝ) (n : ℕ) : ℝ :=
  (secantPairSequence H y x n).1

theorem secantParameterSequence_rec (H : ℝ → ℝ) (y x : ℝ) (n : ℕ) :
    secantParameterSequence H y x (n + 2) =
      (secantParameterSequence H y x (n + 1) * H (secantParameterSequence H y x n) -
        secantParameterSequence H y x n * H (secantParameterSequence H y x (n + 1))) /
      (H (secantParameterSequence H y x n) - H (secantParameterSequence H y x (n + 1))) := rfl

theorem exists_secant_stop_before_twice {m : ℕ} (hm : 0 < m)
    (a b : Fin m → ℝ)
    (hzero : finiteAffineEnvelope hm a b 0 = 0)
    (xs : ℕ → ℝ)
    (hfirst : 0 < xs 1) (hfirstlt : xs 1 < xs 0)
    (hprevious : 0 < finiteAffineEnvelope hm a b (xs 0))
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ finiteAffineEnvelope hm a b w)
    (hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * finiteAffineEnvelope hm a b (xs i) -
        xs i * finiteAffineEnvelope hm a b (xs (i + 1))) /
      (finiteAffineEnvelope hm a b (xs i) - finiteAffineEnvelope hm a b (xs (i + 1)))) :
    ∃ i : ℕ, i < 2 * m ∧
      (finiteAffineEnvelope hm a b (xs (i + 1)) = 0 ∨ xs (i + 2) = 0) := by
  let H := finiteAffineEnvelope hm a b
  have hconv : ConvexOn ℝ Set.univ H := finiteAffineEnvelope_convex hm a b
  by_contra hnostop
  have hnot : ∀ i : ℕ, i < 2 * m → H (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0 := by
    intro i hi
    constructor
    · intro hz
      exact hnostop ⟨i, hi, Or.inl hz⟩
    · intro hz
      exact hnostop ⟨i, hi, Or.inr hz⟩
  have hpair : ∀ n : ℕ, n < 2 * m →
      0 < xs n ∧ 0 < xs (n + 1) ∧ xs (n + 1) < xs n ∧
        xs n ≤ xs 0 ∧ 0 < H (xs n) ∧ 0 < H (xs (n + 1)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have hcur : 0 < H (xs 1) := lt_of_le_of_ne
        (hphase (xs 1) hfirst.le hfirstlt.le)
        (Ne.symm (hnot 0 (by omega)).1)
      exact ⟨hfirst.trans hfirstlt, hfirst, hfirstlt, le_rfl, hprevious, hcur⟩
    | succ n ih =>
      intro hn
      obtain ⟨hprevpos, hcurpos, hlt, hprevbound, hprevgap, hcurgap⟩ := ih (by omega)
      have hprogress := convex_secant_zero_progress hconv hzero hcurpos hlt hcurgap
      have hnextnonneg : 0 ≤ xs (n + 2) := by rw [hrec n]; exact hprogress.2.1
      have hnextlt : xs (n + 2) < xs (n + 1) := by rw [hrec n]; exact hprogress.2.2
      have hnextpos : 0 < xs (n + 2) :=
        lt_of_le_of_ne hnextnonneg (Ne.symm (hnot n (by omega)).2)
      have hcurbound : xs (n + 1) ≤ xs 0 := hlt.le.trans hprevbound
      have hnextbound : xs (n + 2) ≤ xs 0 := hnextlt.le.trans hcurbound
      have hnextgap : 0 < H (xs (n + 2)) := lt_of_le_of_ne
        (hphase (xs (n + 2)) hnextnonneg hnextbound)
        (Ne.symm (by simpa only [Nat.add_assoc] using (hnot (n + 1) hn).1))
      exact ⟨hcurpos, hnextpos, hnextlt, hcurbound, hcurgap, hnextgap⟩
  have hpositive : ∀ k : ℕ, k ≤ 2 * m → 0 < xs k := by
    intro k hk
    cases k with
    | zero => exact hfirst.trans hfirstlt
    | succ k => exact (hpair k (by omega)).2.1
  have hgap : ∀ k : ℕ, k ≤ 2 * m → 0 < H (xs k) := by
    intro k hk
    cases k with
    | zero => exact hprevious
    | succ k => exact (hpair k (by omega)).2.2.2.2.2
  let xf : Fin (2 * m + 1) → ℝ := fun i => xs i.val
  have hanti : StrictAnti xf := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    exact (hpair i.val i.isLt).2.2.1
  have hxfpositive : ∀ i, 0 < xf i := fun i => hpositive i.val (by omega)
  have hxfgap : ∀ i, 0 < H (xf i) := fun i => hgap i.val (by omega)
  have hactive : ∀ i : Fin (2 * m + 1), ∃ j : Fin m, H (xf i) = a j * xf i + b j :=
    fun i => finiteAffineEnvelope_attained hm a b (xf i)
  choose piece hpiece using hactive
  have hcount := secant_nonterminal_query_count_le_twice hconv hzero a b
    (fun j w => finiteAffineEnvelope_major hm a b j w)
    xf hanti hxfpositive hxfgap piece hpiece (fun i hi => by
      change xs (i + 2) =
        (xs (i + 1) * H (xs i) - xs i * H (xs (i + 1))) /
          (H (xs i) - H (xs (i + 1)))
      exact hrec i)
  omega

theorem concrete_secant_sequence_stops {m : ℕ} (hm : 0 < m)
    (a b : Fin m → ℝ) (hzero : finiteAffineEnvelope hm a b 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : 0 < finiteAffineEnvelope hm a b y)
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ y → 0 ≤ finiteAffineEnvelope hm a b w) :
    let H := finiteAffineEnvelope hm a b
    let xs := secantParameterSequence H y x
    ∃ i : ℕ, i < 2 * m ∧ (H (xs (i + 1)) = 0 ∨ xs (i + 2) = 0) :=
  exists_secant_stop_before_twice hm a b hzero
    (secantParameterSequence (finiteAffineEnvelope hm a b) y x)
    hx hxy hy hphase (secantParameterSequence_rec _ y x)

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def nativeReferenceLinear (t : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun q := firstChordValue t q / t
  map_add' q r := by dsimp [firstChordValue]; ring
  map_smul' a q := by dsimp [firstChordValue]; ring

def nativeReferenceFunctional (t : ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (nativeReferenceLinear t).toContinuousLinearMap

theorem nativeReferenceFunctional_scale {t : ℝ} (ht : t ≠ 0) (q : Fin 2 → ℝ) :
    firstChordValue t q = t * nativeReferenceFunctional t q := by
  change firstChordValue t q = t * (firstChordValue t q / t)
  exact (mul_div_cancel₀ _ ht).symm

theorem nativeReferenceFunctional_suppliedPoint {t : ℝ} (ht : t ≠ 0) :
    nativeReferenceFunctional t suppliedPoint = 1 := by
  change ((t - 1) * 0 + t * 1) / t = 1
  simpa only [mul_zero, zero_add, mul_one] using div_self ht

theorem nativeReferenceFunctional_of_coefficient {β : ℝ} (hβ : β < 1) :
    let t := 1 / (1 - β)
    0 < t ∧ ∀ q : Fin 2 → ℝ, nativeReferenceFunctional t q = β * q 0 + q 1 := by
  dsimp only
  have hden : 0 < 1 - β := sub_pos.mpr hβ
  have ht : 0 < 1 / (1 - β) := div_pos (by norm_num) hden
  refine ⟨ht, ?_⟩
  intro q
  change (((1 / (1 - β)) - 1) * q 0 + (1 / (1 - β)) * q 1) /
      (1 / (1 - β)) = β * q 0 + q 1
  field_simp [hden.ne', ht.ne']
  <;> ring

theorem native_reference_reply_level_bounds {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ) (hB : firstChordValue t B = 0)
    (x : ℝ)
    (hgap : 0 < finiteAffineEnvelope hm (fun j => L j B)
      (fun j => L j suppliedPoint - 1) x) :
    0 < firstChordValue t (oracle (suppliedPoint + x • B)) ∧
      firstChordValue t (oracle (suppliedPoint + x • B)) < t := by
  let S := nativeReferenceFunctional t
  have hSp : S suppliedPoint = 1 := nativeReferenceFunctional_suppliedPoint ht.ne'
  have hSB : S B = 0 := by change firstChordValue t B / t = 0; rw [hB, zero_div]
  have hr := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle suppliedPoint B x S hSp hSB).1
  obtain ⟨u, hu, heq, hH⟩ := rayOracle_halfspace_envelope_eq hm L hP horacle suppliedPoint B x hr
  have hone : 1 < 1 / u := by linarith only [hgap, hH]
  have hult : u < 1 := by simpa only [one_mul] using (lt_div_iff₀ hu).mp hone
  have hSq : S (oracle (suppliedPoint + x • B)) = u := by
    rw [heq, map_smul, map_add, map_smul, hSp, hSB]
    change u * (1 + x * 0) = u
    ring
  rw [nativeReferenceFunctional_scale ht.ne']
  change 0 < t * S (oracle (suppliedPoint + x • B)) ∧
    t * S (oracle (suppliedPoint + x • B)) < t
  rw [hSq]
  exact ⟨mul_pos ht hu, by simpa only [mul_one] using mul_lt_mul_of_pos_left hult ht⟩

theorem retained_first_reply_below_new_reference {t β q₀ q₁ : ℝ}
    (hq₀ : 0 < q₀)
    (hgap : (t - 1) * q₀ + t * q₁ < t)
    (hsupport : β * q₀ + q₁ = 1) : β * (-t) + t < 1 := by
  have hs := congrArg (fun r : ℝ => t * r) hsupport
  have hprod : 0 < q₀ * (t * β - t + 1) := by nlinarith only [hs, hgap]
  have hstrict : 0 < t * β - t + 1 := pos_of_mul_pos_right hprod hq₀.le
  nlinarith only [hstrict]

theorem planar_functional_coordinates (S : (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hSp : S suppliedPoint = 1) (q : Fin 2 → ℝ) :
    S q = S (fun k : Fin 2 => if k = 0 then 1 else 0) * q 0 + q 1 := by
  let e : Fin 2 → ℝ := fun k => if k = 0 then 1 else 0
  have hdecomp : q = q 0 • e + q 1 • suppliedPoint := by
    funext k
    fin_cases k
    · change q 0 = q 0 * 1 + q 1 * 0
      ring
    · change q 1 = q 0 * 0 + q 1 * 1
      ring
  calc
    S q = S (q 0 • e + q 1 • suppliedPoint) := congrArg S hdecomp
    _ = S e * q 0 + q 1 := by
      rw [map_add, map_smul, map_smul, hSp]
      change q 0 * S e + q 1 * 1 = S e * q 0 + q 1
      ring

theorem planar_support_recovered_coefficient (S : (Fin 2 → ℝ) →L[ℝ] ℝ)
    (hSp : S suppliedPoint = 1) (q : Fin 2 → ℝ) (hq₀ : q 0 ≠ 0)
    (hSq : S q = 1) :
    ∀ r : Fin 2 → ℝ, S r = ((1 - q 1) / q 0) * r 0 + r 1 := by
  have hq : S (fun k : Fin 2 => if k = 0 then 1 else 0) * q 0 + q 1 = 1 :=
    (planar_functional_coordinates S hSp q).symm.trans hSq
  have hcoef : S (fun k : Fin 2 => if k = 0 then 1 else 0) = (1 - q 1) / q 0 :=
    (eq_div_iff hq₀).mpr (by linarith only [hq])
  intro r
  calc
    S r = S (fun k : Fin 2 => if k = 0 then 1 else 0) * r 0 + r 1 :=
      planar_functional_coordinates S hSp r
    _ = ((1 - q 1) / q 0) * r 0 + r 1 := by rw [hcoef]

theorem native_reference_actual_intersection {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hcurrent : 0 ≤ finiteAffineEnvelope hm (fun j => L j B)
      (fun j => L j suppliedPoint - 1) x)
    (hprevious : 0 < finiteAffineEnvelope hm (fun j => L j B)
      (fun j => L j suppliedPoint - 1) y) :
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
    let current := oracle (suppliedPoint + x • B)
    let previous := oracle (suppliedPoint + y • B)
    let z := (x * H y - y * H x) / (H y - H x)
    0 < firstChordValue t (current - previous) ∧
      firstIntersectionDirection t previous current = suppliedPoint + z • B ∧
      (firstChordValue t previous + firstChordValue t (current - previous) - t = 0 ↔
        H x = 0) ∧
      (firstIntersectionDirection t previous current 0 = 0 ↔ z = 0) := by
  dsimp only
  let S := nativeReferenceFunctional t
  have hSp : S suppliedPoint = 1 := nativeReferenceFunctional_suppliedPoint ht.ne'
  have hSB : S B = 0 := by
    change firstChordValue t B / t = 0
    rw [hB, zero_div]
  have hstep := rayOracle_reference_secant_step hm L hP horacle suppliedPoint B hp
    S hSp hSB hx hxy hcurrent hprevious
  dsimp only at hstep
  let current := oracle (suppliedPoint + x • B)
  let previous := oracle (suppliedPoint + y • B)
  let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
  let z := (x * H y - y * H x) / (H y - H x)
  have hdiff : 0 < S (current - previous) := hstep.1
  have hδ : 0 < firstChordValue t (current - previous) := by
    rw [nativeReferenceFunctional_scale ht.ne']
    exact mul_pos ht hdiff
  have hparameter : firstIntersectionParameter t previous current =
      (1 - S previous) / S (current - previous) := by
    rw [firstIntersectionParameter, nativeReferenceFunctional_scale ht.ne' previous,
      nativeReferenceFunctional_scale ht.ne' (current - previous)]
    change (t - t * S previous) / (t * S (current - previous)) =
      (1 - S previous) / S (current - previous)
    field_simp [ht.ne', hdiff.ne']
    <;> ring
  have hintersection : firstIntersectionDirection t previous current = suppliedPoint + z • B := by
    rw [firstIntersectionDirection, hparameter]
    exact hstep.2.1
  refine ⟨hδ, hintersection, ?_, ?_⟩
  · change (firstChordValue t previous + firstChordValue t (current - previous) - t = 0 ↔
      H x = 0)
    rw [firstChord_test_zero_iff_current_on_reference]
    rw [nativeReferenceFunctional_scale ht.ne' current]
    have hnormalize : t * nativeReferenceFunctional t current = t ↔ S current = 1 := by
      change t * S current = t ↔ S current = 1
      constructor
      · intro heq
        exact mul_left_cancel₀ ht.ne' (by simpa only [mul_one] using heq)
      · intro heq
        rw [heq, mul_one]
    rw [hnormalize]
    exact hstep.2.2.2.1
  · change firstIntersectionDirection t previous current 0 = 0 ↔ z = 0
    rw [hintersection]
    change 0 + z * B 0 = 0 ↔ z = 0
    simp only [zero_add, mul_eq_zero, hB₀, or_false]

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem rayOracle_secant_anchor_common_active {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hcurrent : 0 < finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x)
    (hanchor :
      (x * finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y -
        y * finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x) /
      (finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y -
        finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x) = 0) :
    ∃ j : Fin m, L j p = 1 ∧ L j (oracle (p + y • B)) = 1 ∧
      L j (oracle (p + x • B)) = 1 := by
  let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1)
  have hconv := finiteAffineEnvelope_convex hm (fun j => L j B) (fun j => L j p - 1)
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP p B hp
  have hprogress := convex_secant_zero_progress hconv hzero hx hxy hcurrent
  have hgap : H x < H y := by linarith only [hprogress.1]
  obtain ⟨tx, ty, hty, hscale, heqx, heqy, hHx, hHy, _⟩ :=
    reference_reply_gap_of_envelope_gap hm L hP horacle p B x y S hSp hSB hgap
  have htx : 0 < tx := hty.trans hscale
  have hden : H y - H x ≠ 0 := hprogress.1.ne'
  change (x * H y - y * H x) / (H y - H x) = 0 at hanchor
  have hnum : x * H y - y * H x = 0 :=
    (div_eq_zero_iff.mp hanchor).resolve_right hden
  change H x = 1 / tx - 1 at hHx
  change H y = 1 / ty - 1 at hHy
  have hcross : x * (1 / ty - 1) = y * (1 / tx - 1) := by
    rw [hHx, hHy] at hnum
    linarith only [hnum]
  obtain ⟨hθpos, hθlt, hbracket⟩ := secant_zero_replies_bracket p B hx hxy
    (one_div_pos.mpr htx) (one_div_pos.mpr hty) hcross
  let θ := x * (1 / ty) / (y * (1 / tx))
  have hcombo : oracle (p + x • B) =
      (1 - θ) • p + θ • oracle (p + y • B) := by
    rw [heqx, heqy]
    simpa only [one_div_one_div] using hbracket
  have hrx := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B x S hSp hSB).1
  have hry := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B y S hSp hSB).1
  have hfrontx := (horacle (p + x • B) hrx).1
  have hfronty := (horacle (p + y • B) hry).1
  have hpMem : p ∈ P := by
    rw [hP]
    exact (frontier_finite_halfspaces_active L hP hp).1
  have hyMem : oracle (p + y • B) ∈ P := by
    rw [hP]
    exact (frontier_finite_halfspaces_active L hP hfronty).1
  exact halfspace_common_active_of_positive_combo L hP hpMem hyMem hfrontx
    (sub_pos.mpr hθlt) hθpos (by ring) hcombo

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem secant_query_count_avoiding_known {n m : ℕ} {H : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ H) (hzero : H 0 = 0)
    (a b : Fin m → ℝ) (hmajor : ∀ j t, a j * t + b j ≤ H t)
    (known : Finset (Fin m))
    (x : Fin n → ℝ) (hx : StrictAnti x) (hpositive : ∀ i, 0 < x i)
    (hgap : ∀ i, 0 < H (x i))
    (piece : Fin n → Fin m) (hactive : ∀ i, H (x i) = a (piece i) * x i + b (piece i))
    (hunknown : ∀ i, piece i ∉ known)
    (hrec : ∀ i : ℕ, ∀ hi : i + 2 < n,
      x ⟨i + 2, hi⟩ =
        (x ⟨i + 1, by omega⟩ * H (x ⟨i, by omega⟩) -
          x ⟨i, by omega⟩ * H (x ⟨i + 1, by omega⟩)) /
        (H (x ⟨i, by omega⟩) - H (x ⟨i + 1, by omega⟩))) :
    n ≤ 2 * (m - known.card) := by
  classical
  let U : Finset (Fin m) := knownᶜ
  have hUcard : U.card = m - known.card := by
    simp only [U, Finset.card_compl, Fintype.card_fin]
  let e : U ≃ Fin (m - known.card) := Finset.equivFinOfCardEq hUcard
  let aU : Fin (m - known.card) → ℝ := fun j => a (e.symm j).val
  let bU : Fin (m - known.card) → ℝ := fun j => b (e.symm j).val
  let pieceU : Fin n → Fin (m - known.card) :=
    fun i => e ⟨piece i, Finset.mem_compl.mpr (hunknown i)⟩
  have hmajorU : ∀ j t, aU j * t + bU j ≤ H t := fun j t => hmajor (e.symm j).val t
  have hactiveU : ∀ i, H (x i) = aU (pieceU i) * x i + bU (pieceU i) := by
    intro i
    simpa only [aU, bU, pieceU, Equiv.symm_apply_apply] using hactive i
  exact secant_nonterminal_query_count_le_twice hconv hzero aU bU hmajorU
    x hx hpositive hgap pieceU hactiveU hrec

theorem two_side_query_count_avoiding_known {n k m : ℕ}
    (known : Finset (Fin m)) (positive : Fin n → Fin m) (negative : Fin k → Fin m)
    (hposUnknown : ∀ i, positive i ∉ known) (hnegUnknown : ∀ i, negative i ∉ known)
    (hpos : ∀ i j : Fin n, i.val + 2 ≤ j.val → positive i ≠ positive j)
    (hneg : ∀ i j : Fin k, i.val + 2 ≤ j.val → negative i ≠ negative j)
    (hdisjoint : ∀ i j, positive i ≠ negative j) :
    n + k ≤ 2 * (m - known.card) := by
  classical
  let U : Finset (Fin m) := knownᶜ
  have hUcard : U.card = m - known.card := by
    simp only [U, Finset.card_compl, Fintype.card_fin]
  let e : U ≃ Fin (m - known.card) := Finset.equivFinOfCardEq hUcard
  let p : Fin n → Fin (m - known.card) := fun i =>
    e ⟨positive i, Finset.mem_compl.mpr (hposUnknown i)⟩
  let q : Fin k → Fin (m - known.card) := fun i =>
    e ⟨negative i, Finset.mem_compl.mpr (hnegUnknown i)⟩
  apply two_side_query_count_of_close_disjoint_labels p q
  · intro i j hij heq
    exact hpos i j hij (congrArg Subtype.val (e.injective heq))
  · intro i j hij heq
    exact hneg i j hij (congrArg Subtype.val (e.injective heq))
  · intro i j heq
    exact hdisjoint i j (congrArg Subtype.val (e.injective heq))

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem opposite_reference_points_common_active {d m : ℕ}
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hminus : p - a • B ∈ P) (hplus : p + x • B ∈ P) :
    ∃ j : Fin m, L j p = 1 ∧ L j (p - a • B) = 1 ∧ L j (p + x • B) = 1 := by
  have hden : 0 < a + x := add_pos ha hx
  have hα : 0 < x / (a + x) := div_pos hx hden
  have hβ : 0 < a / (a + x) := div_pos ha hden
  have hab : x / (a + x) + a / (a + x) = 1 := by
    field_simp [hden.ne']
    <;> ring
  have hcombo : p = (x / (a + x)) • (p - a • B) + (a / (a + x)) • (p + x • B) := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hden.ne']
    <;> ring
  obtain ⟨j, hjminus, hjplus, hjp⟩ := halfspace_common_active_of_positive_combo
    L hP hminus hplus hp hα hβ hab hcombo
  exact ⟨j, hjp, hjminus, hjplus⟩

theorem rayOracle_reference_zero_common_active {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hminus : p - a • B ∈ P)
    (hgap : finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x = 0) :
    ∃ j : Fin m, L j p = 1 ∧ L j (oracle (p + x • B)) = 1 := by
  have hr := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle p B x S hSp hSB).1
  have hfix := (rayOracle_halfspace_envelope_zero_iff_fixed hm L hP horacle p B x hr).mp hgap
  have hfront := (horacle (p + x • B) hr).1
  have hplus : p + x • B ∈ P := by
    rw [← hfix, hP]
    exact (frontier_finite_halfspaces_active L hP hfront).1
  obtain ⟨j, hjp, _, hjplus⟩ := opposite_reference_points_common_active L hP p B hp ha hx hminus hplus
  exact ⟨j, hjp, by rw [hfix]; exact hjplus⟩

theorem rayOracle_one_side_terminal_common_active {d m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin d → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (p B : Fin d → ℝ) (hp : p ∈ frontier P)
    (S : (Fin d → ℝ) →L[ℝ] ℝ) (hSp : S p = 1) (hSB : S B = 0)
    {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hxy : x < y)
    (hminus : p - a • B ∈ P)
    (hcurrent : 0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x)
    (hstop : finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x = 0 ∨
      (x * finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y -
        y * finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x) /
      (finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) y -
        finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x) = 0) :
    ∃ j : Fin m, L j p = 1 ∧ L j (oracle (p + x • B)) = 1 := by
  by_cases hz : finiteAffineEnvelope hm (fun j => L j B) (fun j => L j p - 1) x = 0
  · exact rayOracle_reference_zero_common_active hm L hP horacle p B hp S hSp hSB ha hx hminus hz
  · have hpos := lt_of_le_of_ne hcurrent (Ne.symm hz)
    obtain ⟨j, hjp, _, hjcurrent⟩ := rayOracle_secant_anchor_common_active hm L hP horacle
      p B hp S hSp hSB hx hxy hpos (hstop.resolve_left hz)
    exact ⟨j, hjp, hjcurrent⟩

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def storedPlanarPoint (tape : ℤ → ℝ) (a b : ℤ) : Fin 2 → ℝ :=
  fun k => if k = 0 then tape a else tape b

theorem referenceWalkProgram_actual_step {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ y →
      0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1) w)
    (hprevious : 0 < finiteAffineEnvelope hm (fun j => L j B)
      (fun j => L j suppliedPoint - 1) y)
    (tape : ℤ → ℝ) (q : ℕ)
    (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + x • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + x • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + y • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + y • B) 1) :
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
    let z := (x * H y - y * H x) / (H y - H x)
    ∃ c : RayConfiguration,
      rayMachineRun referenceWalkProgram oracle 27
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if H x = 0 ∨ z = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if H x = 0 ∨ z = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = if H x = 0 ∨ z = 0 then
        (suppliedPoint + z • B) i else oracle (suppliedPoint + z • B) i) ∧
      c.tape 5 = (if H x = 0 ∨ z = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if H x = 0 ∨ z = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧
      c.tape 3 = t + 1 ∧
      (c.tape 16 = 0 ↔ H x = 0) ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) ∧
      0 ≤ z ∧ z ≤ x ∧
      (¬ (H x = 0 ∨ z = 0) →
        0 < z ∧ z < x ∧ 0 ≤ H z ∧ 0 < H x ∧ H z < H x) := by
  dsimp only
  let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
  let z := (x * H y - y * H x) / (H y - H x)
  let current := oracle (suppliedPoint + x • B)
  let previous := oracle (suppliedPoint + y • B)
  have hcurrent : 0 ≤ H x := hphase x hx.le hxy.le
  obtain ⟨hδ, hintersection, htest, hanchor⟩ := native_reference_actual_intersection
    hm L hP horacle hp ht B hB hB₀ hx hxy hcurrent hprevious
  have hcurrentTape : storedPlanarPoint tape 0 1 = current := by
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
  have hpreviousTape : storedPlanarPoint tape 5 6 = previous := by
    funext i
    fin_cases i
    · exact h₅
    · exact h₆
  have hDpos : 1 < tape 3 := by rw [hD]; linarith only [ht]
  have hδTape : firstChordValue (tape 3 - 1)
      (storedPlanarPoint tape 0 1 - storedPlanarPoint tape 5 6) ≠ 0 := by
    rw [hD, add_sub_cancel_right, hcurrentTape, hpreviousTape]
    exact hδ.ne'
  have hprogram := referenceWalkProgram_one_iteration oracle tape q hDpos hδTape
  let T := tape 3 - 1
  let previousTape := storedPlanarPoint tape 5 6
  let currentTape := storedPlanarPoint tape 0 1
  let δ := firstChordValue T (currentTape - previousTape)
  let test := firstChordValue T previousTape + δ - T
  let r := firstIntersectionDirection T previousTape currentTape
  have hprogram' : ∃ c : RayConfiguration,
      rayMachineRun referenceWalkProgram oracle 27
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
      c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
      c.tape 14 = δ ∧ c.tape 16 = test ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := hprogram
  have hT : T = t := by dsimp only [T]; rw [hD]; ring
  have htest' : test = 0 ↔ H x = 0 := by
    dsimp only [test, δ, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact htest
  have hr : r = suppliedPoint + z • B := by
    dsimp only [r, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact hintersection
  have hanchor' : r 0 = 0 ↔ z = 0 := by
    dsimp only [r, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact hanchor
  have hstop : (test = 0 ∨ r 0 = 0) ↔ (H x = 0 ∨ z = 0) := or_congr htest' hanchor'
  simp only [hstop] at hprogram'
  obtain ⟨c, hrun, hpc, hhead, hq, hheader, hprev5, hprev6, hsave0, hsave1, hD', _, htest16, hframe⟩ := hprogram'
  have hconv := finiteAffineEnvelope_convex hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP suppliedPoint B hp
  have hbounds : 0 ≤ z ∧ z ≤ x := by
    rcases eq_or_lt_of_le hcurrent with hz | hpos
    · have hz' : H x = 0 := hz.symm
      have hden : H y ≠ 0 := hprevious.ne'
      have hzx : z = x := by
        dsimp only [z]
        rw [hz', mul_zero, sub_zero, sub_zero, mul_div_cancel_right₀ x hden]
      rw [hzx]
      exact ⟨hx.le, le_rfl⟩
    · have hs := convex_secant_zero_progress hconv hzero hx hxy hpos
      exact ⟨hs.2.1, hs.2.2.le⟩
  refine ⟨c, hrun, hpc, hhead, hq, ?_, hprev5, hprev6, hsave0, hsave1, hD'.trans hD,
    ?_, hframe, hbounds.1, hbounds.2, ?_⟩
  · intro i
    simpa only [hr] using hheader i
  · rw [htest16]
    exact htest'
  · intro hcontinue
    have hzpos : 0 < z := lt_of_le_of_ne hbounds.1
      (Ne.symm (fun hz => hcontinue (Or.inr hz)))
    have hxpos : 0 < H x := lt_of_le_of_ne hcurrent
      (Ne.symm (fun hz => hcontinue (Or.inl hz)))
    have hzlt : z < x := (convex_secant_zero_progress hconv hzero hx hxy hxpos).2.2
    exact ⟨hzpos, hzlt, hphase z hbounds.1 (hbounds.2.trans hxy.le), hxpos,
      convex_gap_strictly_smaller_parameter hconv hzero hzpos hzlt hxpos⟩

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem referenceWalkProgram_actual_exit_step
    (program : List RayInstruction)
    (hprefix : ∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ y →
      0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1) w)
    (hprevious : 0 < finiteAffineEnvelope hm (fun j => L j B)
      (fun j => L j suppliedPoint - 1) y)
    (tape : ℤ → ℝ) (q : ℕ)
    (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + x • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + x • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + y • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + y • B) 1) :
    let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
    let z := (x * H y - y * H x) / (H y - H x)
    ∃ c : RayConfiguration,
      rayMachineRun program oracle (if H x = 0 then 23 else if z = 0 then 24 else 27)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if H x = 0 ∨ z = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if H x = 0 ∨ z = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = if H x = 0 ∨ z = 0 then
        (suppliedPoint + z • B) i else oracle (suppliedPoint + z • B) i) ∧
      c.tape 5 = (if H x = 0 ∨ z = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if H x = 0 ∨ z = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧
      c.tape 3 = t + 1 ∧
      (c.tape 16 = 0 ↔ H x = 0) ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) ∧
      0 ≤ z ∧ z ≤ x ∧
      (¬ (H x = 0 ∨ z = 0) →
        0 < z ∧ z < x ∧ 0 ≤ H z ∧ 0 < H x ∧ H z < H x) := by
  dsimp only
  let H := finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
  let z := (x * H y - y * H x) / (H y - H x)
  let current := oracle (suppliedPoint + x • B)
  let previous := oracle (suppliedPoint + y • B)
  have hcurrent : 0 ≤ H x := hphase x hx.le hxy.le
  obtain ⟨hδ, hintersection, htest, hanchor⟩ := native_reference_actual_intersection
    hm L hP horacle hp ht B hB hB₀ hx hxy hcurrent hprevious
  have hcurrentTape : storedPlanarPoint tape 0 1 = current := by
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
  have hpreviousTape : storedPlanarPoint tape 5 6 = previous := by
    funext i
    fin_cases i
    · exact h₅
    · exact h₆
  have hDpos : 1 < tape 3 := by rw [hD]; linarith only [ht]
  have hδTape : firstChordValue (tape 3 - 1)
      (storedPlanarPoint tape 0 1 - storedPlanarPoint tape 5 6) ≠ 0 := by
    rw [hD, add_sub_cancel_right, hcurrentTape, hpreviousTape]
    exact hδ.ne'
  have hprogram := referenceWalkProgram_exit_iteration program hprefix oracle tape q hDpos hδTape
  let T := tape 3 - 1
  let previousTape := storedPlanarPoint tape 5 6
  let currentTape := storedPlanarPoint tape 0 1
  let δ := firstChordValue T (currentTape - previousTape)
  let test := firstChordValue T previousTape + δ - T
  let r := firstIntersectionDirection T previousTape currentTape
  have hprogram' : ∃ c : RayConfiguration,
      rayMachineRun program oracle (if test = 0 then 23 else if r 0 = 0 then 24 else 27)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = (if test = 0 ∨ r 0 = 0 then 27 else 0) ∧ c.head = 0 ∧
      c.queries = q + (if test = 0 ∨ r 0 = 0 then 0 else 1) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = if test = 0 ∨ r 0 = 0 then r i else oracle r i) ∧
      c.tape 5 = (if test = 0 ∨ r 0 = 0 then tape 5 else tape 0) ∧
      c.tape 6 = (if test = 0 ∨ r 0 = 0 then tape 6 else tape 1) ∧
      c.tape 9 = tape 0 ∧ c.tape 10 = tape 1 ∧ c.tape 3 = tape 3 ∧
      c.tape 14 = δ ∧ c.tape 16 = test ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := hprogram
  have hT : T = t := by dsimp only [T]; rw [hD]; ring
  have htest' : test = 0 ↔ H x = 0 := by
    dsimp only [test, δ, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact htest
  have hr : r = suppliedPoint + z • B := by
    dsimp only [r, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact hintersection
  have hanchor' : r 0 = 0 ↔ z = 0 := by
    dsimp only [r, currentTape, previousTape]
    rw [hT, hcurrentTape, hpreviousTape]
    exact hanchor
  have hstop : (test = 0 ∨ r 0 = 0) ↔ (H x = 0 ∨ z = 0) := or_congr htest' hanchor'
  simp only [htest', hanchor', hstop] at hprogram'
  obtain ⟨c, hrun, hpc, hhead, hq, hheader, hprev5, hprev6, hsave0, hsave1, hD', _, htest16, hframe⟩ := hprogram'
  have hconv := finiteAffineEnvelope_convex hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP suppliedPoint B hp
  have hbounds : 0 ≤ z ∧ z ≤ x := by
    rcases eq_or_lt_of_le hcurrent with hz | hpos
    · have hz' : H x = 0 := hz.symm
      have hden : H y ≠ 0 := hprevious.ne'
      have hzx : z = x := by
        dsimp only [z]
        rw [hz', mul_zero, sub_zero, sub_zero, mul_div_cancel_right₀ x hden]
      rw [hzx]
      exact ⟨hx.le, le_rfl⟩
    · have hs := convex_secant_zero_progress hconv hzero hx hxy hpos
      exact ⟨hs.2.1, hs.2.2.le⟩
  refine ⟨c, hrun, hpc, hhead, hq, ?_, hprev5, hprev6, hsave0, hsave1, hD'.trans hD,
    ?_, hframe, hbounds.1, hbounds.2, ?_⟩
  · intro i
    simpa only [hr] using hheader i
  · rw [htest16]
    exact htest'
  · intro hcontinue
    have hzpos : 0 < z := lt_of_le_of_ne hbounds.1
      (Ne.symm (fun hz => hcontinue (Or.inr hz)))
    have hxpos : 0 < H x := lt_of_le_of_ne hcurrent
      (Ne.symm (fun hz => hcontinue (Or.inl hz)))
    have hzlt : z < x := (convex_secant_zero_progress hconv hzero hx hxy hxpos).2.2
    exact ⟨hzpos, hzlt, hphase z hbounds.1 (hbounds.2.trans hxy.le), hxpos,
      convex_gap_strictly_smaller_parameter hconv hzero hzpos hzlt hxpos⟩

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

def nativeGap {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ) (B : Fin 2 → ℝ) : ℝ → ℝ :=
  finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)

private theorem run_add_rpr {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

theorem referenceWalkProgram_actual_prefix {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    (xs : ℕ → ℝ)
    (hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
        (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1))))
    (hfirst : 0 < xs 1) (hfirstlt : xs 1 < xs 0)
    (hprevious : 0 < nativeGap hm L B (xs 0))
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w)
    (tape : ℤ → ℝ) (q : ℕ)
    (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + xs 1 • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + xs 1 • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + xs 0 • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + xs 0 • B) 1)
    (n : ℕ)
    (hnostop : ∀ i : ℕ, i < n →
      nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0) :
    ∃ c : RayConfiguration,
      rayMachineRun referenceWalkProgram oracle (27 * n)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = 0 ∧ c.head = 0 ∧ c.queries = q + n ∧
      c.tape 0 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
      c.tape 1 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
      c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
      c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
      c.tape 3 = t + 1 ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) ∧
      0 < xs (n + 1) ∧ xs (n + 1) < xs n ∧ xs n ≤ xs 0 ∧
      0 < nativeGap hm L B (xs n) ∧ 0 ≤ nativeGap hm L B (xs (n + 1)) := by
  revert hnostop
  induction n with
  | zero =>
    intro _
    refine ⟨{pc := 0, head := 0, tape := tape, queries := q}, rfl, rfl, rfl, ?_,
      h₀, h₁, h₅, h₆, hD, ?_, hfirst, hfirstlt, le_rfl, hprevious,
      hphase (xs 1) hfirst.le hfirstlt.le⟩
    · simp only [Nat.add_zero]
    · intro _ _
      rfl
  | succ n ih =>
    intro hnostop
    obtain ⟨c, hrun, hpc, hhead, hq, hc₀, hc₁, hc₅, hc₆, hcD, hcframe,
      hx, hxy, hybound, hygap, hxgap⟩ := ih (fun i hi => hnostop i (by omega))
    have hcut : ∀ w : ℝ, 0 ≤ w → w ≤ xs n →
        0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1) w :=
      fun w hw hwy => hphase w hw (hwy.trans hybound)
    have hmacro := referenceWalkProgram_actual_step hm L hP horacle hp ht B hB hB₀
      hx hxy hcut hygap c.tape (q + n) hcD hc₀ hc₁ hc₅ hc₆
    dsimp only at hmacro
    have hnext := (hrec n).symm
    dsimp only [nativeGap] at hnext
    rw [hnext] at hmacro
    have hcontinue : ¬ (finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) := by
      rintro (hz | hz)
      · exact (hnostop n (by omega)).1 hz
      · exact (hnostop n (by omega)).2 hz
    simp only [if_neg hcontinue] at hmacro
    obtain ⟨c', hstep, hpc', hhead', hq', hheader', hprev5', hprev6', _, _, hD', _,
      hframe', _, _, hgeometry⟩ := hmacro
    obtain ⟨hnextpos, hnextlt, hnextgap, hcurgap, _⟩ := hgeometry hcontinue
    have hcEta : {pc := 0, head := 0, tape := c.tape, queries := q + n} = c := by
      rcases c with ⟨pc, head, data, count⟩
      change pc = 0 at hpc
      change head = 0 at hhead
      change count = q + n at hq
      change ({pc := 0, head := 0, tape := data, queries := q + n} : RayConfiguration) =
        {pc := pc, head := head, tape := data, queries := count}
      rw [hpc, hhead, hq]
    rw [hcEta] at hstep
    refine ⟨c', ?_, hpc', hhead', ?_, hheader' 0, hheader' 1,
      hprev5'.trans hc₀, hprev6'.trans hc₁, hD', ?_, hnextpos, hnextlt,
      hxy.le.trans hybound, hcurgap, hnextgap⟩
    · rw [Nat.mul_succ, run_add_rpr, hrun, Option.bind_some, hstep]
    · simpa only [Nat.add_assoc] using hq'
    · intro j hj
      exact (hframe' j hj).trans (hcframe j hj)

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem run_add_rper {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

theorem referenceWalkProgram_actual_prefix_with_exit
    (program : List RayInstruction)
    (hprefix : ∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    (xs : ℕ → ℝ)
    (hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
        (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1))))
    (hfirst : 0 < xs 1) (hfirstlt : xs 1 < xs 0)
    (hprevious : 0 < nativeGap hm L B (xs 0))
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w)
    (tape : ℤ → ℝ) (q : ℕ)
    (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + xs 1 • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + xs 1 • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + xs 0 • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + xs 0 • B) 1)
    (n : ℕ)
    (hnostop : ∀ i : ℕ, i < n →
      nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0) :
    ∃ c : RayConfiguration,
      rayMachineRun program oracle (27 * n)
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = 0 ∧ c.head = 0 ∧ c.queries = q + n ∧
      c.tape 0 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
      c.tape 1 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
      c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
      c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
      c.tape 3 = t + 1 ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) ∧
      0 < xs (n + 1) ∧ xs (n + 1) < xs n ∧ xs n ≤ xs 0 ∧
      0 < nativeGap hm L B (xs n) ∧ 0 ≤ nativeGap hm L B (xs (n + 1)) := by
  revert hnostop
  induction n with
  | zero =>
    intro _
    refine ⟨{pc := 0, head := 0, tape := tape, queries := q}, rfl, rfl, rfl, ?_,
      h₀, h₁, h₅, h₆, hD, ?_, hfirst, hfirstlt, le_rfl, hprevious,
      hphase (xs 1) hfirst.le hfirstlt.le⟩
    · simp only [Nat.add_zero]
    · intro _ _
      rfl
  | succ n ih =>
    intro hnostop
    obtain ⟨c, hrun, hpc, hhead, hq, hc₀, hc₁, hc₅, hc₆, hcD, hcframe,
      hx, hxy, hybound, hygap, hxgap⟩ := ih (fun i hi => hnostop i (by omega))
    have hcut : ∀ w : ℝ, 0 ≤ w → w ≤ xs n →
        0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1) w :=
      fun w hw hwy => hphase w hw (hwy.trans hybound)
    have hmacro := referenceWalkProgram_actual_exit_step program hprefix hm L hP horacle hp ht B hB hB₀
      hx hxy hcut hygap c.tape (q + n) hcD hc₀ hc₁ hc₅ hc₆
    dsimp only at hmacro
    have hnext := (hrec n).symm
    dsimp only [nativeGap] at hnext
    rw [hnext] at hmacro
    have hcontinue : ¬ (finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) := by
      rintro (hz | hz)
      · exact (hnostop n (by omega)).1 hz
      · exact (hnostop n (by omega)).2 hz
    have hcurrent_ne : finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) ≠ 0 := (hnostop n (by omega)).1
    have hnext_ne : xs (n + 2) ≠ 0 := (hnostop n (by omega)).2
    simp only [if_neg hcontinue, if_neg hcurrent_ne, if_neg hnext_ne] at hmacro
    obtain ⟨c', hstep, hpc', hhead', hq', hheader', hprev5', hprev6', _, _, hD', _,
      hframe', _, _, hgeometry⟩ := hmacro
    obtain ⟨hnextpos, hnextlt, hnextgap, hcurgap, _⟩ := hgeometry hcontinue
    have hcEta : {pc := 0, head := 0, tape := c.tape, queries := q + n} = c := by
      rcases c with ⟨pc, head, data, count⟩
      change pc = 0 at hpc
      change head = 0 at hhead
      change count = q + n at hq
      change ({pc := 0, head := 0, tape := data, queries := q + n} : RayConfiguration) =
        {pc := pc, head := head, tape := data, queries := count}
      rw [hpc, hhead, hq]
    rw [hcEta] at hstep
    refine ⟨c', ?_, hpc', hhead', ?_, hheader' 0, hheader' 1,
      hprev5'.trans hc₀, hprev6'.trans hc₁, hD', ?_, hnextpos, hnextlt,
      hxy.le.trans hybound, hcurgap, hnextgap⟩
    · rw [Nat.mul_succ, run_add_rper, hrun, Option.bind_some, hstep]
    · simpa only [Nat.add_assoc] using hq'
    · intro j hj
      exact (hframe' j hj).trans (hcframe j hj)

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

private theorem run_add_rpes {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration) :
    rayMachineRun program oracle (a + b) c =
      (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, rayMachineRun, Option.bind_some]
  | succ a ih => simp only [Nat.succ_add, rayMachineRun, ih, Option.bind_assoc]

theorem referenceWalkProgram_exits_of_first_guard
    (program : List RayInstruction)
    (hprefix : ∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    (xs : ℕ → ℝ)
    (hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
        (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1))))
    (hfirst : 0 < xs 1) (hfirstlt : xs 1 < xs 0)
    (hprevious : 0 < nativeGap hm L B (xs 0))
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w)
    (tape : ℤ → ℝ) (q : ℕ) (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + xs 1 • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + xs 1 • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + xs 0 • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + xs 0 • B) 1)
    (n : ℕ)
    (hnostop : ∀ i : ℕ, i < n → nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0)
    (hstop : nativeGap hm L B (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) :
    ∃ c : RayConfiguration,
      rayMachineRun program oracle
        (27 * n + (if nativeGap hm L B (xs (n + 1)) = 0 then 23 else 24))
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = 27 ∧ c.head = 0 ∧ c.queries = q + n ∧
      c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
      c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
      c.tape 9 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
      c.tape 10 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
      c.tape 3 = t + 1 ∧
      (c.tape 16 = 0 ↔ nativeGap hm L B (xs (n + 1)) = 0) ∧
      (∀ i : Fin 2, c.tape (i.val : ℤ) = (suppliedPoint + xs (n + 2) • B) i) ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := by
  obtain ⟨c, hrun, hpc, hhead, hq, hc₀, hc₁, hc₅, hc₆, hcD, hcframe,
    hx, hxy, hybound, hygap, _⟩ := referenceWalkProgram_actual_prefix_with_exit program hprefix hm L hP horacle hp
      ht B hB hB₀ xs hrec hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ n hnostop
  have hcut : ∀ w : ℝ, 0 ≤ w → w ≤ xs n →
      0 ≤ finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1) w :=
    fun w hw hwy => hphase w hw (hwy.trans hybound)
  have hmacro := referenceWalkProgram_actual_exit_step program hprefix hm L hP horacle hp ht B hB hB₀
    hx hxy hcut hygap c.tape (q + n) hcD hc₀ hc₁ hc₅ hc₆
  dsimp only at hmacro
  have hnext := (hrec n).symm
  dsimp only [nativeGap] at hnext
  rw [hnext] at hmacro
  change finiteAffineEnvelope hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
    (xs (n + 1)) = 0 ∨ xs (n + 2) = 0 at hstop
  have htime : (if finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) = 0 then 23
      else if xs (n + 2) = 0 then 24 else 27) =
      (if finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) = 0 then 23 else 24) := by
    by_cases hz : finiteAffineEnvelope hm (fun j => L j B)
        (fun j => L j suppliedPoint - 1) (xs (n + 1)) = 0
    · simp only [if_pos hz]
    · have hnz : xs (n + 2) = 0 := hstop.resolve_left hz
      simp only [if_neg hz, if_pos hnz]
  rw [htime] at hmacro
  simp only [if_pos hstop, Nat.add_zero] at hmacro
  obtain ⟨b, hstep, hbpc, hbhead, hbq, hbheader, hbprev5, hbprev6, hbsave0, hbsave1,
    hbD, hbflag, hbframe, _, _, _⟩ := hmacro
  have hcEta : {pc := 0, head := 0, tape := c.tape, queries := q + n} = c := by
    rcases c with ⟨pc, head, data, count⟩
    change pc = 0 at hpc
    change head = 0 at hhead
    change count = q + n at hq
    change ({pc := 0, head := 0, tape := data, queries := q + n} : RayConfiguration) =
      {pc := pc, head := head, tape := data, queries := count}
    rw [hpc, hhead, hq]
  rw [hcEta] at hstep
  refine ⟨b, ?_, hbpc, hbhead, hbq, hbprev5.trans hc₅, hbprev6.trans hc₆,
    hbsave0.trans hc₀, hbsave1.trans hc₁, hbD, hbflag, hbheader, ?_⟩
  · rw [run_add_rpes, hrun, Option.bind_some]
    exact hstep
  · intro j hj
    exact (hbframe j hj).trans (hcframe j hj)

theorem referenceWalkProgram_phase_exits
    (program : List RayInstruction)
    (hprefix : ∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (hy : 0 < nativeGap hm L B y)
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ y → 0 ≤ nativeGap hm L B w)
    (tape : ℤ → ℝ) (q : ℕ) (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + x • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + x • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + y • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + y • B) 1) :
    ∃ n : ℕ, n < 2 * m ∧ ∃ steps : ℕ, steps ≤ 27 * (n + 1) ∧ ∃ c : RayConfiguration,
      rayMachineRun program oracle steps
        {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
      c.pc = 27 ∧ c.head = 0 ∧ c.queries = q + n ∧
      c.tape 3 = t + 1 ∧ (c.tape 16 = 0 ∨ c.tape 0 = 0) ∧
      (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j) := by
  classical
  let H := nativeGap hm L B
  let xs := secantParameterSequence H y x
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP suppliedPoint B hp
  have hex : ∃ i : ℕ, i < 2 * m ∧ (H (xs (i + 1)) = 0 ∨ xs (i + 2) = 0) :=
    concrete_secant_sequence_stops hm (fun j => L j B) (fun j => L j suppliedPoint - 1)
      hzero hx hxy hy hphase
  let n := Nat.find hex
  have hn : n < 2 * m := (Nat.find_spec hex).1
  have hstop : H (xs (n + 1)) = 0 ∨ xs (n + 2) = 0 := (Nat.find_spec hex).2
  have hnostop : ∀ i : ℕ, i < n → H (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0 := by
    intro i hi
    constructor
    · intro hz
      exact (Nat.find_min hex hi) ⟨hi.trans hn, Or.inl hz⟩
    · intro hz
      exact (Nat.find_min hex hi) ⟨hi.trans hn, Or.inr hz⟩
  have hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
        (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1))) :=
    secantParameterSequence_rec H y x
  obtain ⟨c, hrun, hpc, hhead, hq, _, _, _, _, hD', hflag, hheader, hframe⟩ :=
    referenceWalkProgram_exits_of_first_guard program hprefix hm L hP horacle hp ht B hB hB₀
      xs hrec hx hxy hy hphase tape q hD h₀ h₁ h₅ h₆ n hnostop hstop
  let steps := 27 * n + (if nativeGap hm L B (xs (n + 1)) = 0 then 23 else 24)
  have hsteps : steps ≤ 27 * (n + 1) := by
    dsimp only [steps]
    split_ifs <;> omega
  refine ⟨n, hn, steps, hsteps, c, hrun, hpc, hhead, hq, hD', ?_, hframe⟩
  · rcases hstop with hline | hanchor
    · exact Or.inl (hflag.mpr hline)
    · right
      have hh := hheader (0 : Fin 2)
      rw [hanchor, zero_smul, add_zero] at hh
      exact hh

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem native_first_reference_data {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {q | ∀ j, L j q ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P) :
    let τ := oracle firstDirection 1
    let B := secondDirection τ - suppliedPoint
    let H := nativeGap hm L B
    0 < τ ∧ 0 < B 0 ∧ firstChordValue τ B = 0 ∧ H 0 = 0 ∧
      (∀ z : ℝ, 0 ≤ z → 0 ≤ H z) ∧
      oracle firstDirection = suppliedPoint - (1 + τ) • B ∧
      suppliedPoint - (1 + τ) • B ∈ P ∧
      suppliedPoint + (1 : ℝ) • B = secondDirection τ ∧
      firstMidpointDirection τ = suppliedPoint + (1 / 2 : ℝ) • B ∧
      (oracle (secondDirection τ) ≠ secondDirection τ → 0 < H 1) := by
  dsimp only
  obtain ⟨hτ, hfirst⟩ := first_query_response horacle
  let τ := oracle firstDirection 1
  let B := secondDirection τ - suppliedPoint
  let u : Fin 2 → ℝ := fun k => if k = 0 then 1 else 0
  have hdir : suppliedPoint - (1 : ℝ) • u = firstDirection := by
    funext k
    fin_cases k <;> norm_num [u, suppliedPoint, firstDirection, firstResponse]
  have hfirstNe : firstDirection ≠ 0 := by
    intro hz
    have hh := congrFun hz 0
    norm_num [firstDirection, firstResponse] at hh
  have hr : suppliedPoint - (1 : ℝ) • u ≠ 0 := by rw [hdir]; exact hfirstNe
  have hreply : oracle (suppliedPoint - (1 : ℝ) • u) =
      τ • (suppliedPoint - (1 : ℝ) • u) := by
    rw [hdir, hfirst]
    funext k
    fin_cases k <;> simp [τ, firstResponse, firstDirection]
  have hR₂ : (τ / (1 + τ)) • ((1 : ℝ) • u) + (2 / (1 + τ)) • suppliedPoint =
      secondDirection τ := by
    funext k
    fin_cases k <;> simp [u, suppliedPoint, secondDirection]
  have hdata := first_reference_chord_data hm L hP horacle suppliedPoint u hp
    (ε := (1 : ℝ)) hτ hr hreply
  dsimp only at hdata
  rw [hR₂] at hdata
  have hden : 1 + τ ≠ 0 := by linarith only [hτ]
  have hBpos : 0 < B 0 := by
    change 0 < τ / (1 + τ) - 0
    simpa only [sub_zero] using div_pos hτ (by linarith only [hτ])
  have hBkernel : firstChordValue τ B = 0 := by
    change (τ - 1) * (τ / (1 + τ) - 0) + τ * (2 / (1 + τ) - 1) = 0
    field_simp [hden]
    <;> ring
  have hnegative : oracle firstDirection = suppliedPoint - (1 + τ) • B := by
    have hh := hdata.2.2.2.1
    rw [hdir] at hh
    dsimp only [τ, B]
    simpa only [neg_smul, sub_eq_add_neg] using hh
  have hminus : suppliedPoint - (1 + τ) • B ∈ P := by
    rw [← hnegative, hP]
    exact (frontier_finite_halfspaces_active L hP (horacle firstDirection hfirstNe).1).1
  have hRone : suppliedPoint + (1 : ℝ) • B = secondDirection τ := by
    dsimp only [B]
    rw [one_smul]
    abel
  have hmid : firstMidpointDirection τ = suppliedPoint + (1 / 2 : ℝ) • B := by
    exact hdata.2.2.2.2
  refine ⟨hτ, hBpos, hBkernel, hdata.1, hdata.2.2.1, hnegative, hminus, hRone, hmid, ?_⟩
  intro hnonfixed
  have hrOne : suppliedPoint + (1 : ℝ) • B ≠ 0 := by
    rw [hRone]
    exact (secondDirection_geometry hτ).2.2.1
  have hnonfixOne : oracle (suppliedPoint + (1 : ℝ) • B) ≠ suppliedPoint + (1 : ℝ) • B := by
    rw [hRone]
    exact hnonfixed
  exact (rayOracle_nonnegative_envelope_pos_iff_nonfixed hm L hP horacle suppliedPoint B 1
    hrOne (hdata.2.2.1 1 (by norm_num))).mpr hnonfixOne

end Grunbaum2003.RayPlanar

namespace Grunbaum2003.RayPlanar

theorem one_side_actual_prefix_query_budget {m : ℕ} (hm : 0 < m)
    (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
    {P : Set (Fin 2 → ℝ)} (hP : P = {v | ∀ j, L j v ≤ 1})
    {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (horacle : IsPolytopeRayOracle P oracle)
    (hp : suppliedPoint ∈ frontier P)
    {t : ℝ} (ht : 0 < t) (B : Fin 2 → ℝ)
    (hB : firstChordValue t B = 0) (hB₀ : B 0 ≠ 0)
    (xs : ℕ → ℝ)
    (hrec : ∀ i : ℕ, xs (i + 2) =
      (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
        (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1))))
    (hfirst : 0 < xs 1) (hfirstlt : xs 1 < xs 0)
    (hprevious : 0 < nativeGap hm L B (xs 0))
    (hphase : ∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w)
    (tape : ℤ → ℝ) (q : ℕ) (hD : tape 3 = t + 1)
    (h₀ : tape 0 = oracle (suppliedPoint + xs 1 • B) 0)
    (h₁ : tape 1 = oracle (suppliedPoint + xs 1 • B) 1)
    (h₅ : tape 5 = oracle (suppliedPoint + xs 0 • B) 0)
    (h₆ : tape 6 = oracle (suppliedPoint + xs 0 • B) 1)
    (n : ℕ)
    (hnostop : ∀ i : ℕ, i < n → nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0)
    (known : Finset (Fin m))
    (hsafe : ∀ z : ℝ, 0 ≤ z → z ≤ xs 0 →
      ∀ j ∈ known, L j (oracle (suppliedPoint + z • B)) < 1) :
    n + 1 ≤ 2 * (m - known.card) ∧ 3 + n ≤ 2 * (m - known.card) + 2 := by
  classical
  let H := nativeGap hm L B
  have hdata : ∀ k : ℕ, k ≤ n →
      0 < xs k ∧ xs (k + 1) < xs k ∧ xs k ≤ xs 0 ∧ 0 < H (xs k) := by
    intro k hk
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcurpos, hlt, hbound, hgap, _⟩ :=
      referenceWalkProgram_actual_prefix hm L hP horacle hp ht B hB hB₀ xs hrec
        hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ k
        (fun i hi => hnostop i (by omega))
    exact ⟨hcurpos.trans hlt, hlt, hbound, hgap⟩
  let x : Fin (n + 1) → ℝ := fun i => xs i.val
  have hpositive : ∀ i, 0 < x i := fun i => (hdata i.val (by omega)).1
  have hgap : ∀ i, 0 < H (x i) := fun i => (hdata i.val (by omega)).2.2.2
  have hanti : StrictAnti x := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    exact (hdata i.val (by omega)).2.1
  let S := nativeReferenceFunctional t
  have hSp : S suppliedPoint = 1 := nativeReferenceFunctional_suppliedPoint ht.ne'
  have hSB : S B = 0 := by
    change firstChordValue t B / t = 0
    rw [hB, zero_div]
  have hlabels : ∀ i : Fin (n + 1), ∃ j : Fin m,
      H (x i) = L j B * x i + (L j suppliedPoint - 1) ∧ j ∉ known := by
    intro i
    have hr := (rayOracle_reference_level_iff_envelope_zero hm L hP horacle
      suppliedPoint B (x i) S hSp hSB).1
    obtain ⟨_, j, hj⟩ := frontier_finite_halfspaces_active L hP (horacle (suppliedPoint + x i • B) hr).1
    refine ⟨j, rayOracle_active_halfspace_envelope hm L hP horacle suppliedPoint B (x i) hr j hj, ?_⟩
    intro hknown
    have hs := hsafe (x i) (hpositive i).le (hdata i.val (by omega)).2.2.1 j hknown
    rw [hj] at hs
    exact (lt_irrefl (1 : ℝ)) hs
  choose piece hactive hunknown using hlabels
  have hconv : ConvexOn ℝ Set.univ H := finiteAffineEnvelope_convex hm _ _
  have hzero : H 0 = 0 := halfspace_envelope_zero_at_boundary hm L hP suppliedPoint B hp
  have hcount := secant_query_count_avoiding_known hconv hzero
    (fun j => L j B) (fun j => L j suppliedPoint - 1)
    (fun j z => finiteAffineEnvelope_major hm (fun k => L k B)
      (fun k => L k suppliedPoint - 1) j z) known
    x hanti hpositive hgap piece hactive hunknown (fun i hi => by
      change xs (i + 2) =
        (xs (i + 1) * H (xs i) - xs i * H (xs (i + 1))) /
          (H (xs i) - H (xs (i + 1)))
      exact hrec i)
  exact ⟨hcount, by omega⟩

end Grunbaum2003.RayPlanar

namespace Grunbaum2003

theorem rayMachine_planar_reference_walk_and_one_sided_budget :
    ∃ (suppliedPoint : Fin 2 → ℝ)
      (firstDirection : Fin 2 → ℝ)
      (secondDirection : ℝ → Fin 2 → ℝ)
      (firstMidpointDirection : ℝ → Fin 2 → ℝ)
      (firstChordValue : ℝ → (Fin 2 → ℝ) → ℝ)
      (nativeReferenceFunctional : ℝ → (Fin 2 → ℝ) →L[ℝ] ℝ)
      (nativeGap : ∀ {m : ℕ}, 0 < m → (Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ) → (Fin 2 → ℝ) → ℝ → ℝ)
      (secondQueryProgram : List RayInstruction)
      (firstMidpointProgram : List RayInstruction)
      (referenceWalkProgram : List RayInstruction),
      suppliedPoint = (fun i => if i = 0 then 0 else 1) ∧
      firstDirection = (fun i => if i = 0 then -1 else 1) ∧
      (∀ t : ℝ, secondDirection t = fun i => if i = 0 then t / (1 + t) else 2 / (1 + t)) ∧
      (∀ t : ℝ, firstMidpointDirection t = (1 / 2 : ℝ) • (suppliedPoint + secondDirection t)) ∧
      (∀ (t : ℝ) (x : Fin 2 → ℝ), firstChordValue t x = (t - 1) * x 0 + t * x 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        0 < tape 1 →
        ∃ c : RayConfiguration,
          rayMachineRun secondQueryProgram oracle 6
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          secondQueryProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (secondDirection (tape 1)) i) ∧
          c.tape 3 = tape 1 + 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        1 < tape 3 →
        ∃ c : RayConfiguration,
          rayMachineRun firstMidpointProgram oracle 12
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          firstMidpointProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (firstMidpointDirection (tape 3 - 1)) i) ∧
          c.tape 5 = tape 0 ∧ c.tape 6 = tape 1 ∧ c.tape 3 = tape 3) ∧
      (∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
        {P : Set (Fin 2 → ℝ)}, P = {q | ∀ j, L j q ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        let τ := oracle firstDirection 1
        let B := secondDirection τ - suppliedPoint
        let H := nativeGap hm L B
        0 < τ ∧ 0 < B 0 ∧ firstChordValue τ B = 0 ∧ H 0 = 0 ∧
          (∀ z : ℝ, 0 ≤ z → 0 ≤ H z) ∧
          oracle firstDirection = suppliedPoint - (1 + τ) • B ∧
          suppliedPoint - (1 + τ) • B ∈ P ∧
          suppliedPoint + (1 : ℝ) • B = secondDirection τ ∧
          firstMidpointDirection τ = suppliedPoint + (1 / 2 : ℝ) • B ∧
          (oracle (secondDirection τ) ≠ secondDirection τ → 0 < H 1)) ∧
      (∀ (program : List RayInstruction),
        (∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) →
        ∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
          {P : Set (Fin 2 → ℝ)}, P = {v | ∀ j, L j v ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        ∀ {t : ℝ}, 0 < t → ∀ (B : Fin 2 → ℝ),
        firstChordValue t B = 0 → B 0 ≠ 0 →
        ∀ (xs : ℕ → ℝ),
        (∀ i : ℕ, xs (i + 2) =
          (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
            (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1)))) →
        0 < xs 1 → xs 1 < xs 0 →
        0 < nativeGap hm L B (xs 0) →
        (∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w) →
        ∀ (tape : ℤ → ℝ) (q : ℕ), tape 3 = t + 1 →
        tape 0 = oracle (suppliedPoint + xs 1 • B) 0 →
        tape 1 = oracle (suppliedPoint + xs 1 • B) 1 →
        tape 5 = oracle (suppliedPoint + xs 0 • B) 0 →
        tape 6 = oracle (suppliedPoint + xs 0 • B) 1 →
        ∀ (n : ℕ),
        (∀ i : ℕ, i < n → nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0) →
        ((∀ (known : Finset (Fin m)),
            (∀ z : ℝ, 0 ≤ z → z ≤ xs 0 → ∀ j ∈ known, L j (oracle (suppliedPoint + z • B)) < 1) →
            n + 1 ≤ 2 * (m - known.card) ∧ 3 + n ≤ 2 * (m - known.card) + 2) ∧
          ((nativeGap hm L B (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) →
            (∀ {a : ℝ}, 0 < a → suppliedPoint - a • B ∈ P →
              ∃ j : Fin m, L j suppliedPoint = 1 ∧ L j (oracle (suppliedPoint + xs (n + 1) • B)) = 1) ∧
            ∃ c : RayConfiguration,
              rayMachineRun program oracle
                (27 * n + (if nativeGap hm L B (xs (n + 1)) = 0 then 23 else 24))
                {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
              c.pc = 27 ∧ c.head = 0 ∧ c.queries = q + n ∧
              c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
              c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
              c.tape 9 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
              c.tape 10 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
              c.tape 3 = t + 1 ∧
              (c.tape 16 = 0 ↔ nativeGap hm L B (xs (n + 1)) = 0) ∧
              (∀ i : Fin 2, c.tape (i.val : ℤ) = (suppliedPoint + xs (n + 2) • B) i) ∧
              (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j)))) := by
  refine ⟨RayPlanar.suppliedPoint, RayPlanar.firstDirection, RayPlanar.secondDirection,
    RayPlanar.firstMidpointDirection, RayPlanar.firstChordValue,
    RayPlanar.nativeReferenceFunctional, @RayPlanar.nativeGap,
    RayPlanar.secondQueryProgram, RayPlanar.firstMidpointProgram,
    RayPlanar.referenceWalkProgram,
    rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    RayPlanar.secondQueryProgram_correct,
    RayPlanar.firstMidpointProgram_correct,
    ?_, ?_⟩
  · intro m hm L P hP oracle horacle hp
    exact RayPlanar.native_first_reference_data hm L hP horacle hp
  · intro program hprefix m hm L P hP oracle horacle hp t ht B hB hB₀ xs hrec hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ n hnostop
    constructor
    · intro known hsafe
      exact RayPlanar.one_side_actual_prefix_query_budget hm L hP horacle hp ht B hB hB₀ xs hrec
        hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ n hnostop known hsafe
    · intro hstop
      refine ⟨?_, RayPlanar.referenceWalkProgram_exits_of_first_guard program hprefix hm L hP horacle hp
        ht B hB hB₀ xs hrec hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ n hnostop hstop⟩
      intro a ha hminus
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hxpos, hxy, hybound, hygap, hxgap⟩ :=
        RayPlanar.referenceWalkProgram_actual_prefix hm L hP horacle hp ht B hB hB₀ xs hrec
          hfirst hfirstlt hprevious hphase tape q hD h₀ h₁ h₅ h₆ n hnostop
      let S := RayPlanar.nativeReferenceFunctional t
      have hSp : S RayPlanar.suppliedPoint = 1 := RayPlanar.nativeReferenceFunctional_suppliedPoint ht.ne'
      have hSB : S B = 0 := by
        change RayPlanar.firstChordValue t B / t = 0
        rw [hB, zero_div]
      have hstop' : RayPlanar.finiteAffineEnvelope hm (fun j => L j B) (fun j => L j RayPlanar.suppliedPoint - 1) (xs (n + 1)) = 0 ∨
          (xs (n + 1) * RayPlanar.finiteAffineEnvelope hm (fun j => L j B) (fun j => L j RayPlanar.suppliedPoint - 1) (xs n) -
            xs n * RayPlanar.finiteAffineEnvelope hm (fun j => L j B) (fun j => L j RayPlanar.suppliedPoint - 1) (xs (n + 1))) /
          (RayPlanar.finiteAffineEnvelope hm (fun j => L j B) (fun j => L j RayPlanar.suppliedPoint - 1) (xs n) -
            RayPlanar.finiteAffineEnvelope hm (fun j => L j B) (fun j => L j RayPlanar.suppliedPoint - 1) (xs (n + 1))) = 0 := by
        rcases hstop with h1 | h2
        · exact Or.inl h1
        · right
          have hrec_n := hrec n
          dsimp only [RayPlanar.nativeGap] at hrec_n
          exact hrec_n.symm.trans h2
      exact RayPlanar.rayOracle_one_side_terminal_common_active hm L hP horacle
        RayPlanar.suppliedPoint B hp S hSp hSB ha hxpos hxy hminus hxgap hstop'

end Grunbaum2003
end

theorem solution :
    ∃ (suppliedPoint : Fin 2 → ℝ)
      (firstDirection : Fin 2 → ℝ)
      (secondDirection : ℝ → Fin 2 → ℝ)
      (firstMidpointDirection : ℝ → Fin 2 → ℝ)
      (firstChordValue : ℝ → (Fin 2 → ℝ) → ℝ)
      (nativeReferenceFunctional : ℝ → (Fin 2 → ℝ) →L[ℝ] ℝ)
      (nativeGap : ∀ {m : ℕ}, 0 < m → (Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ) → (Fin 2 → ℝ) → ℝ → ℝ)
      (secondQueryProgram : List Grunbaum2003.RayInstruction)
      (firstMidpointProgram : List Grunbaum2003.RayInstruction)
      (referenceWalkProgram : List Grunbaum2003.RayInstruction),
      suppliedPoint = (fun i => if i = 0 then 0 else 1) ∧
      firstDirection = (fun i => if i = 0 then -1 else 1) ∧
      (∀ t : ℝ, secondDirection t = fun i => if i = 0 then t / (1 + t) else 2 / (1 + t)) ∧
      (∀ t : ℝ, firstMidpointDirection t = (1 / 2 : ℝ) • (suppliedPoint + secondDirection t)) ∧
      (∀ (t : ℝ) (x : Fin 2 → ℝ), firstChordValue t x = (t - 1) * x 0 + t * x 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        0 < tape 1 →
        ∃ c : Grunbaum2003.RayConfiguration,
          Grunbaum2003.rayMachineRun secondQueryProgram oracle 6
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          secondQueryProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (secondDirection (tape 1)) i) ∧
          c.tape 3 = tape 1 + 1) ∧
      (∀ (oracle : (Fin 2 → ℝ) → Fin 2 → ℝ) (tape : ℤ → ℝ) (q : ℕ),
        1 < tape 3 →
        ∃ c : Grunbaum2003.RayConfiguration,
          Grunbaum2003.rayMachineRun firstMidpointProgram oracle 12
            {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
          firstMidpointProgram[c.pc]? = some .halt ∧ c.head = 0 ∧ c.queries = q + 1 ∧
          (∀ i : Fin 2, c.tape (i.val : ℤ) = oracle (firstMidpointDirection (tape 3 - 1)) i) ∧
          c.tape 5 = tape 0 ∧ c.tape 6 = tape 1 ∧ c.tape 3 = tape 3) ∧
      (∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
        {P : Set (Fin 2 → ℝ)}, P = {q | ∀ j, L j q ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        let τ := oracle firstDirection 1
        let B := secondDirection τ - suppliedPoint
        let H := nativeGap hm L B
        0 < τ ∧ 0 < B 0 ∧ firstChordValue τ B = 0 ∧ H 0 = 0 ∧
          (∀ z : ℝ, 0 ≤ z → 0 ≤ H z) ∧
          oracle firstDirection = suppliedPoint - (1 + τ) • B ∧
          suppliedPoint - (1 + τ) • B ∈ P ∧
          suppliedPoint + (1 : ℝ) • B = secondDirection τ ∧
          firstMidpointDirection τ = suppliedPoint + (1 / 2 : ℝ) • B ∧
          (oracle (secondDirection τ) ≠ secondDirection τ → 0 < H 1)) ∧
      (∀ (program : List Grunbaum2003.RayInstruction),
        (∀ k : ℕ, k < 27 → program[k]? = referenceWalkProgram[k]?) →
        ∀ {m : ℕ} (hm : 0 < m) (L : Fin m → (Fin 2 → ℝ) →L[ℝ] ℝ)
          {P : Set (Fin 2 → ℝ)}, P = {v | ∀ j, L j v ≤ 1} →
        ∀ {oracle : (Fin 2 → ℝ) → (Fin 2 → ℝ)}, Grunbaum2003.IsPolytopeRayOracle P oracle →
        suppliedPoint ∈ frontier P →
        ∀ {t : ℝ}, 0 < t → ∀ (B : Fin 2 → ℝ),
        firstChordValue t B = 0 → B 0 ≠ 0 →
        ∀ (xs : ℕ → ℝ),
        (∀ i : ℕ, xs (i + 2) =
          (xs (i + 1) * nativeGap hm L B (xs i) - xs i * nativeGap hm L B (xs (i + 1))) /
            (nativeGap hm L B (xs i) - nativeGap hm L B (xs (i + 1)))) →
        0 < xs 1 → xs 1 < xs 0 →
        0 < nativeGap hm L B (xs 0) →
        (∀ w : ℝ, 0 ≤ w → w ≤ xs 0 → 0 ≤ nativeGap hm L B w) →
        ∀ (tape : ℤ → ℝ) (q : ℕ), tape 3 = t + 1 →
        tape 0 = oracle (suppliedPoint + xs 1 • B) 0 →
        tape 1 = oracle (suppliedPoint + xs 1 • B) 1 →
        tape 5 = oracle (suppliedPoint + xs 0 • B) 0 →
        tape 6 = oracle (suppliedPoint + xs 0 • B) 1 →
        ∀ (n : ℕ),
        (∀ i : ℕ, i < n → nativeGap hm L B (xs (i + 1)) ≠ 0 ∧ xs (i + 2) ≠ 0) →
        ((∀ (known : Finset (Fin m)),
            (∀ z : ℝ, 0 ≤ z → z ≤ xs 0 → ∀ j ∈ known, L j (oracle (suppliedPoint + z • B)) < 1) →
            n + 1 ≤ 2 * (m - known.card) ∧ 3 + n ≤ 2 * (m - known.card) + 2) ∧
          ((nativeGap hm L B (xs (n + 1)) = 0 ∨ xs (n + 2) = 0) →
            (∀ {a : ℝ}, 0 < a → suppliedPoint - a • B ∈ P →
              ∃ j : Fin m, L j suppliedPoint = 1 ∧ L j (oracle (suppliedPoint + xs (n + 1) • B)) = 1) ∧
            ∃ c : Grunbaum2003.RayConfiguration,
              Grunbaum2003.rayMachineRun program oracle
                (27 * n + (if nativeGap hm L B (xs (n + 1)) = 0 then 23 else 24))
                {pc := 0, head := 0, tape := tape, queries := q} = some c ∧
              c.pc = 27 ∧ c.head = 0 ∧ c.queries = q + n ∧
              c.tape 5 = oracle (suppliedPoint + xs n • B) 0 ∧
              c.tape 6 = oracle (suppliedPoint + xs n • B) 1 ∧
              c.tape 9 = oracle (suppliedPoint + xs (n + 1) • B) 0 ∧
              c.tape 10 = oracle (suppliedPoint + xs (n + 1) • B) 1 ∧
              c.tape 3 = t + 1 ∧
              (c.tape 16 = 0 ↔ nativeGap hm L B (xs (n + 1)) = 0) ∧
              (∀ i : Fin 2, c.tape (i.val : ℤ) = (suppliedPoint + xs (n + 2) • B) i) ∧
              (∀ j : ℤ, j < 0 ∨ 16 < j → c.tape j = tape j)))) :=
  Grunbaum2003.rayMachine_planar_reference_walk_and_one_sided_budget
