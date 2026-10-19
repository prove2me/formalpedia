-- Prove2me | solution 1 for OAI.Erdos3.scalarCubeFamily_localize_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:27:12.164597+00:00
-- url     : https://prove2.me/submissions/4e59eb00-5f64-4ded-8bc8-132c2c7e5f5a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B137
import Theorems.Thm_OAI_Erdos3_ScalarCubeLocalizationData_localize_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_family_localized_cells (n : ℕ)
    (X E C T : Fin n → Type*) [∀ i, Fintype (X i)]
    [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (a : ∀ i, X i → E i)
    (cell : ∀ i, C i → T i → E i) (Good : ∀ i, C i → Prop)
    (τ : Fin (n + 1) → ℝ)
    (localize : ∀ i (H : E i → ℂ), (∀ x, ‖H x‖ ≤ 1) →
      τ i.castSucc ≤ ‖(p i).complexMean (fun x => H (a i x))‖ →
      ∃ c, Good i c ∧ τ i.succ ≤ ‖𝔼 t, H (cell i c t)‖)
    (F : (∀ i, E i) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi p).complexMean (fun x => F (fun i => a i (x i)))‖) :
    ∃ c : ∀ i, C i, (∀ i, Good i (c i)) ∧
      τ (Fin.last n) ≤ ‖𝔼 t : ∀ i, T i, F (fun i => cell i (c i) (t i))‖ := by
  induction n with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    rw [expect_empty_tuple]
    rw [FiniteProbabilityWeights.complexMean_empty_tuple] at hbias
    have he : (fun i : Fin 0 => a i (Fin.elim0 i)) =
        (fun i : Fin 0 => cell i (Fin.elim0 i) (Fin.elim0 i)) := Subsingleton.elim _ _
    rw [he] at hbias
    exact hbias
  | succ n ih =>
    let q := FiniteProbabilityWeights.pi (fun i : Fin n => p i.succ)
    let H (x : E 0) := q.complexMean (fun y => F (Fin.cons x (fun i => a i.succ (y i))))
    have hH (x : E 0) : ‖H x‖ ≤ 1 :=
      (q.norm_complexMean_le_mean_norm _).trans
        ((q.mean_mono (fun y => hF _)).trans_eq (q.mean_const 1))
    have hfirst : τ (0 : Fin (n + 1)).castSucc ≤
        ‖(p 0).complexMean (fun x => H (a 0 x))‖ := by
      rw [FiniteProbabilityWeights.complexMean_pi_fin_cons] at hbias
      simp only [dependent_fin_cons_map] at hbias
      exact hbias
    obtain ⟨c0, hc0, hmiddle⟩ := localize 0 H hH hfirst
    let G (y : ∀ i : Fin n, E i.succ) := 𝔼 t : T 0, F (Fin.cons (cell 0 c0 t) y)
    have hG (y) : ‖G y‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans
        ((Finset.expect_le_expect (fun t _ => hF _)).trans_eq (Fintype.expect_const 1))
    have htail : (τ (Fin.succ 0)) ≤ ‖q.complexMean (fun y => G (fun i => a i.succ (y i)))‖ := by
      rw [q.complexMean_finset_expect]
      exact hmiddle
    obtain ⟨c, hc, hlast⟩ := ih
      (fun i => X i.succ) (fun i => E i.succ) (fun i => C i.succ) (fun i => T i.succ)
      (fun i => p i.succ) (fun i => a i.succ) (fun i => cell i.succ) (fun i => Good i.succ)
      (fun i => τ i.succ) (fun i => localize i.succ) G hG htail
    refine ⟨Fin.cons c0 c, ?_, ?_⟩
    · intro i
      exact Fin.cases hc0 (fun j => hc j) i
    · have he (t0 : T 0) (t : ∀ i : Fin n, T i.succ) :
          (fun i => cell i (Fin.cons c0 c i) (Fin.cons t0 t i)) =
          Fin.cons (cell 0 c0 t0) (fun i => cell i.succ (c i) (t i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hmean : (𝔼 t : ∀ i : Fin (n + 1), T i,
          F (fun i => cell i (Fin.cons c0 c i) (t i))) =
          𝔼 t : ∀ i : Fin n, T i.succ, G (fun i => cell i.succ (c i) (t i)) := by
        rw [expect_dependent_fin_cons]
        simp only [he]
        exact Finset.expect_comm _ _ _
      rw [hmean]
      exact hlast

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem cellLength_pos : 0 < d.cellLength :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).1

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeFamily_localize_s2_oai {n : ℕ} (I : Fin n → Type*)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (d : ∀ j, ScalarCubeLocalizationData (I j)) (τ : Fin (n + 1) → ℝ)
    (hτ : ∀ j : Fin n, 0 < τ j.succ) (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (F : (∀ j, Option (I j) → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖) :
    ∃ k : ∀ j, Option (I j) → Fin (d j).cellCount,
      (∀ j (t : Option (I j) → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain (I j)) ∧
      τ (Fin.last n) ≤ ‖𝔼 t : ∀ j, Option (I j) → Fin (d j).cellLength,
        F (fun j => (d j).cell (k j) (t j))‖ := by
  let : ∀ j, Nonempty (Option (I j) → Fin (d j).cellLength) :=
    fun j => ⟨fun _ => ⟨0, (d j).cellLength_pos⟩⟩
  exact exists_finite_family_localized_cells n
    (fun j => IntegerScalarCubeBox (I j) (d j).length) (fun j => Option (I j) → ℝ)
    (fun j => Option (I j) → Fin (d j).cellCount) (fun j => Option (I j) → Fin (d j).cellLength)
    (fun j => (d j).source) (fun j => (d j).point) (fun j => (d j).cell)
    (fun j k => ∀ t, (d j).cell k t ∈ scalarCubeDomain (I j)) τ
    (fun j H hH h => (d j).localize_s2 (hτ j) (herror j) H hH h) F hF hbias

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.scalarCubeFamily_localize_s2_oai.{u_1} := @OAI.Erdos3.scalarCubeFamily_localize_s2_oai.{u_1}
