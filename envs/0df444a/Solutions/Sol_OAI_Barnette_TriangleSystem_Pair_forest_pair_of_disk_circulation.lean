-- Prove2me | solution 1 for OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:08:39.194872+00:00
-- url     : https://prove2.me/submissions/d2fc8294-f8c3-461e-ac7f-d896456643d4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/PairPolynomials.lean:L423-L445
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Theorems.Thm_OAI_Barnette_TriangleSystem_OppositeCycle_fixed_second_state_cancels
import Theorems.Thm_OAI_Barnette_TriangleSystem_oppositeCycle_nonempty

-- ---- from OAI.Combinatorics.Hamiltonian.TriangleSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

namespace State

variable {T} {X : Set V}

end State

theorem indexDelta_antisymm : ∀ i j : Fin 3, indexDelta i j = -indexDelta j i := by
  decide

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.PairPolynomials ----
namespace OAI

/-! First nonzero coefficients of paired-state polynomials. -/

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem common_phase_sum_ne_zero {D : Type*} (s : Finset D) (hs : s.Nonempty)
    (c : D → ℕ) (p : D → ℂ[X]) (a : D → ℝ)
    (ha : ∀ d ∈ s, 0 < a d)
    (hp : ∀ d ∈ s, (p d).coeff 0 = (a d : ℂ)) :
    (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)) ≠ 0 := by
  classical
  obtain ⟨d₀, hd₀, hmin⟩ := s.exists_min_image c hs
  let m := c d₀
  let t := s.filter (fun d => c d = m)
  have ht : t.Nonempty := ⟨d₀, Finset.mem_filter.mpr ⟨hd₀, rfl⟩⟩
  have hpos : 0 < ∑ d ∈ t, a d := by
    exact Finset.sum_pos (fun d hd => ha d (Finset.mem_filter.mp hd).1) ht
  have hterm (d : D) (hd : d ∈ s) :
      (C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 := by
    rw [coeff_C_mul, coeff_X_pow_mul']
    by_cases heq : c d = m
    · simp only [heq, le_refl, ite_true, Nat.sub_self, hp d hd]
    · have hlt : m < c d := lt_of_le_of_ne (hmin d hd) (Ne.symm heq)
      simp only [heq, not_le.mpr hlt, ite_false, mul_zero]
  have hcoeff :
      (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        (-Complex.I) ^ m * (∑ d ∈ t, a d : ℝ) := by
    rw [finsetSum_coeff]
    calc
      _ = ∑ d ∈ s, if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 :=
        Finset.sum_congr rfl hterm
      _ = _ := by
        simp only [t, Finset.sum_filter, Complex.ofReal_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp only [Complex.ofReal_zero, mul_zero]
  intro hz
  have hnz : (-Complex.I) ^ m * ((∑ d ∈ t, a d : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast ne_of_gt hpos)
  apply hnz
  rw [← hcoeff, hz, coeff_zero]

theorem linearProduct_coeff_one {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 1 = ∑ t ∈ s, a t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearProduct, coeff_one]
  | @insert t s ht ih =>
    rw [linearProduct, Finset.prod_insert ht, mul_coeff_one]
    change (1 + C (a t) * X).coeff 0 * (linearProduct s a).coeff 1 +
      (1 + C (a t) * X).coeff 1 * (linearProduct s a).coeff 0 = _
    simp [ih, Finset.sum_insert ht, add_comm, coeff_one]

theorem cycle_difference_divX_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    (divX (linearProduct s a - linearProduct s b)).coeff 0 =
      (∑ t ∈ s, a t) - ∑ t ∈ s, b t := by
  rw [coeff_divX, zero_add, coeff_sub, linearProduct_coeff_one, linearProduct_coeff_one]

theorem cycle_difference_eq_X_mul_divX {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    linearProduct s a - linearProduct s b =
      X * divX (linearProduct s a - linearProduct s b) := by
  have h := X_mul_divX_add (linearProduct s a - linearProduct s b)
  simpa using h.symm

end Barnette

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem phase_sum {K : Type*} (s : Finset K) (a : K → ℤ)
    (ha : ∀ k ∈ s, 3 ∣ a k) : phase (∑ k ∈ s, a k) = ∏ k ∈ s, phase (a k) := by
  classical
  unfold phase
  rw [Int.sum_div ha]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, zpow_add₀ Complex.I_ne_zero]
    congr 1
    exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))

theorem phase_neg_of_disk {n : ℤ} (hn : n = 3 ∨ n = -3) : phase (-n) = -phase n := by
  rcases hn with rfl | rfl <;> norm_num

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

theorem orient_delta_sum (P : @Pair A V T X) (b : CycleClass P.next → Bool)
    (c : CycleClass P.next) :
    (∑ t ∈ P.cycleFaces c, indexDelta ((P.orient b).val.left.val t)
        ((P.orient b).val.right.val t)) =
      if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  rw [cycleDelta]
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    exact indexDelta_antisymm _ _

theorem orient_rawIndexSum (P : @Pair A V T X) (b : CycleClass P.next → Bool) :
    rawIndexSum (P.orient b).val.left (P.orient b).val.right =
      ∑ c, if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  unfold rawIndexSum
  rw [← Finset.sum_fiberwise Finset.univ (classOf P.next)]
  apply Finset.sum_congr rfl
  intro c _
  exact P.orient_delta_sum b c

theorem orient_phase (P : @Pair A V T X)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) :
    phase (rawIndexSum (P.orient b).val.left (P.orient b).val.right) =
      ∏ c, if b c then -phase (P.cycleDelta c) else phase (P.cycleDelta c) := by
  classical
  rw [P.orient_rawIndexSum b, phase_sum]
  · apply Finset.prod_congr rfl
    intro c _
    cases hb : b c <;> simp [phase_neg_of_disk (hdisk c)]
  · intro c _
    rcases hdisk c with h | h <;> cases b c <;> simp [h]

theorem orient_weight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (b : CycleClass P.next → Bool) : stateWeight w (P.orient b).val.right =
      ∏ c, if b c then P.cycleLeftWeight w c else P.cycleRightWeight w c := by
  classical
  unfold stateWeight linearProduct
  rw [← Finset.prod_fiberwise Finset.univ (classOf P.next)]
  apply Finset.prod_congr rfl
  intro c _
  change (∏ t ∈ P.cycleFaces c, _) = _
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte, cycleRightWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, cycleLeftWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl

theorem orient_term (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) : term w (P.orient b).val =
      ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
        else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
  classical
  rw [term, P.orient_phase hdisk, P.orient_weight, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  cases b c <;> simp

theorem group_sum_product (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3) :
    (∑ Q : P.Group, term w Q.val) =
      ∏ c, C (phase (P.cycleDelta c)) *
        (P.cycleRightWeight w c - P.cycleLeftWeight w c) := by
  classical
  rw [← Fintype.sum_equiv P.groupEquiv _ (fun Q : P.Group => term w Q.val)
    (fun _ => rfl)]
  calc
    _ = ∑ b : CycleClass P.next → Bool,
        ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
      apply Finset.sum_congr rfl
      intro b _
      exact P.orient_term w hdisk b
    _ = ∏ c, ∑ b : Bool, if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c :=
      (Fintype.prod_sum (ι := CycleClass P.next) (κ := fun _ => Bool)
        (fun c b => if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c _
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true]
      ring

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

theorem cycle_diff_coeff_one (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) :
    (divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)).coeff 0 =
      (P.cycleSlope w c : ℂ) := by
  rw [cycleRightWeight, cycleLeftWeight, cycle_difference_divX_coeff_zero]
  simp only [cycleSlope, Complex.ofReal_sub, Complex.ofReal_sum]

theorem cycle_factor_witness (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next)
    (hsign : (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
      C (phase (P.cycleDelta c)) * (P.cycleRightWeight w c - P.cycleLeftWeight w c) =
        C (-Complex.I) * (Polynomial.X * q) := by
  rcases hsign with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · refine ⟨divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      P.cycleSlope w c, hs, P.cycle_diff_coeff_one w c, ?_⟩
    rw [hd, phase_neg_three]
    congr 1
    exact cycle_difference_eq_X_mul_divX _ _ _
  · refine ⟨-divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      -P.cycleSlope w c, neg_pos.mpr hs, ?_, ?_⟩
    · rw [coeff_neg, P.cycle_diff_coeff_one, Complex.ofReal_neg]
    · rw [hd, phase_three]
      have heq : P.cycleRightWeight w c - P.cycleLeftWeight w c =
          Polynomial.X * divX (P.cycleRightWeight w c - P.cycleLeftWeight w c) :=
        cycle_difference_eq_X_mul_divX _ _ _
      calc
        _ = C Complex.I * (Polynomial.X *
            divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)) := congrArg _ heq
        _ = _ := by simp only [map_neg, mul_neg, neg_mul, neg_neg]

theorem sum_groups (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ d : @GroupIndex A V T X, ∑ Q : d.representative.Group, term w Q.val := by
  classical
  rw [← Fintype.sum_fiberwise groupIndex (term w)]
  apply Finset.sum_congr rfl
  intro d _
  exact Fintype.sum_equiv d.fiberEquivGroup _ _ (fun _ => rfl)

theorem total_sum_ne_zero (hex : Nonempty (@Pair A V T X)) (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    (∑ P : @Pair A V T X, term w P) ≠ 0 := by
  classical
  let D := @GroupIndex A V T X
  have hnonempty : (Finset.univ : Finset D).Nonempty :=
    ⟨hex.some.groupIndex, Finset.mem_univ _⟩
  have hw : ∀ d : D, ∀ c : CycleClass d.representative.next,
      ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
        C (phase (d.representative.cycleDelta c)) *
          (d.representative.cycleRightWeight w c - d.representative.cycleLeftWeight w c) =
            C (-Complex.I) * (Polynomial.X * q) := by
    intro d c
    exact d.representative.cycle_factor_witness w c (hsign d.representative c)
  choose q a ha hq hf using hw
  have h := common_phase_sum_ne_zero Finset.univ hnonempty
    (fun d : D => Fintype.card (CycleClass d.representative.next))
    (fun d => ∏ c, q d c) (fun d => ∏ c, a d c)
    (fun d _ => Finset.prod_pos (fun c _ => ha d c)) (by
      intro d _
      rw [coeff_zero_prod, Complex.ofReal_prod]
      exact Finset.prod_congr rfl (fun c _ => hq d c))
  rw [sum_groups]
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  rw [d.representative.group_sum_product w (fun c => by
    rcases hsign d.representative c with ⟨hd, _⟩ | ⟨hd, _⟩
    · exact Or.inr hd
    · exact Or.inl hd)]
  calc
    _ = ∏ c, C (-Complex.I) * (Polynomial.X * q d c) :=
      Finset.prod_congr rfl (fun c _ => hf d c)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← map_pow]

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

theorem sum_second_states (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ s : T.State X, ∑ r : T.Partners s,
        C (phase (rawIndexSum r.val s)) * stateWeight w s := by
  classical
  rw [← Fintype.sum_fiberwise right (term w)]
  apply Finset.sum_congr rfl
  intro s _
  apply Fintype.sum_equiv (secondFiberEquiv s)
  intro P
  change C (phase (rawIndexSum P.val.left P.val.right)) * stateWeight w P.val.right = _
  rw [P.property]
  rfl

theorem forest_pair_of_disk_circulation (hex : Nonempty (@Pair A V T X))
    (hdisk : ∀ (s : T.State X) (C : T.OppositeCycle s) (r : T.Partners s),
      C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ P : @Pair A V T X, (T.oppositeGraph P.right).IsAcyclic := by
  classical
  by_contra hforest
  have hcyclic (P : @Pair A V T X) : ¬(T.oppositeGraph P.right).IsAcyclic :=
    fun h => hforest ⟨P, h⟩
  apply total_sum_ne_zero hex w hsign
  rw [sum_second_states]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hp : Nonempty (T.Partners s)
  · let P : @Pair A V T X := ⟨(hp.some.val, s), hp.some.property⟩
    obtain ⟨C⟩ := T.oppositeCycle_nonempty s (hcyclic P)
    simpa only [Polynomial.smul_eq_C_mul] using
      C.fixed_second_state_cancels (hdisk s C) (stateWeight w s)
  · have : IsEmpty (T.Partners s) := not_nonempty_iff.mp hp
    exact Finset.sum_eq_zero (fun r _ => isEmptyElim r)

end TriangleSystem.Pair
end Barnette

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.TriangleSystem OAI.Barnette.TriangleSystem.Pair
open scoped BigOperators Polynomial
open Polynomial


theorem solution : type_of% @_root_.OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation := @_root_.OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation
