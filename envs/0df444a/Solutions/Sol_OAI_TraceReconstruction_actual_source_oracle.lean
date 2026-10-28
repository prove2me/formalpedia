-- Prove2me | solution 1 for OAI.TraceReconstruction.actual_source_oracle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T09:59:30.142994+00:00
-- url     : https://prove2.me/submissions/e8f44dd6-b80b-4c87-b571-ec8068fb3a5b

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_OAIQ9Tr002
import Theorems.Thm_OAI_TraceReconstruction_source_reference_clipped_exists

section
-- module Solutions.OAIQ9_TR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Binomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Binomial

Fair and biased binomial laws, generating series, differences, concentration, Gaussian overlap, hidden counts, and local lower bounds.
-/

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

/-! ## Quantitative fair-binomial anti-concentration

A direct inductive bound, avoiding an unformalized appeal to Stirling.
It is one of the estimates needed for signed binomial smoothing and
for the local/global anchor kernels.
-/


/-! ## Discrete convolution estimates for the hidden displacement kernels -/

/-! The probability generating series of the fair binomial kernel. -/

theorem prouhetSeries_succ_coeff (s : ℕ) (z : ℤ) :
    (prouhetSeries (s + 1)).coeff z =
    (prouhetSeries s).coeff z - (prouhetSeries s).coeff (z - (2 ^ s : ℕ)) := by
  rw [prouhetSeries, Finset.prod_range_succ, mul_sub, mul_one]
  change (prouhetSeries s - prouhetSeries s *
    (AddMonoidAlgebra.single 1 1 : IntSeries) ^ (2 ^ s)).coeff z = _
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  simp only [AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one,
    AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

/-- The exact generating polynomial from the manuscript has unit signed
    coefficients at every index 0,...,2^s-1, and no other coefficients. -/
theorem prouhetSeries_coeff_spec (s : ℕ) :
    (∀ z : ℤ, (z < 0 ∨ (2 ^ s : ℕ) ≤ z) → (prouhetSeries s).coeff z = 0) ∧
    (∀ z : ℤ, 0 ≤ z → z < (2 ^ s : ℕ) → |(prouhetSeries s).coeff z| = 1) := by
  induction s with
  | zero =>
    have hcoeff (z : ℤ) : (prouhetSeries 0).coeff z = if 0 = z then 1 else 0 := by
      change (AddMonoidAlgebra.single 0 (1 : ℝ)).coeff z = _
      exact Finsupp.single_apply
    constructor
    · intro z hz
      rw [hcoeff, ite_eq_right]
      norm_num only [pow_zero, Nat.cast_one] at hz
      omega
    · intro z h0 h1
      have hz : z = 0 := by norm_num only [pow_zero, Nat.cast_one] at h1; omega
      subst hz
      rw [hcoeff, ite_eq_left rfl, abs_one]
  | succ s ih =>
    have hp : (0 : ℤ) < (2 ^ s : ℕ) := by positivity
    have hd : ((2 ^ (s + 1) : ℕ) : ℤ) = 2 * (2 ^ s : ℕ) := by push_cast; ring
    constructor
    · intro z hz
      rw [prouhetSeries_succ_coeff]
      rcases hz with hz | hz
      · rw [ih.1 z (Or.inl hz), ih.1 _ (Or.inl (by omega)), sub_zero]
      · rw [hd] at hz
        rw [ih.1 z (Or.inr (by omega)), ih.1 _ (Or.inr (by omega)), sub_zero]
    · intro z h0 h1
      rw [hd] at h1
      rw [prouhetSeries_succ_coeff]
      by_cases hz : z < (2 ^ s : ℕ)
      · rw [ih.1 (z - (2 ^ s : ℕ)) (Or.inl (by omega)), sub_zero]
        exact ih.2 z h0 hz
      · rw [ih.1 z (Or.inr (by omega)), zero_sub, abs_neg]
        exact ih.2 _ (by omega) (by omega)


/-! ## Nonfair anti-concentration without an assumed Stirling estimate -/

/-! ## Gaussian overlap by exponential tilting of the exact binomial law -/

end TraceReconstruction

namespace TraceReconstruction

/-- Exact moment generating function, including both endpoint channels. -/
theorem binomialMass_mgf (n : ℕ) (p t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) =
      (1 - p + p * Real.exp t) ^ n := by
  rw [add_comm (1 - p), add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [show t * (k : ℝ) = (k : ℝ) * t by ring, Real.exp_nat_mul, mul_pow]
  unfold binomialMass
  ring

theorem binomialMass_mgf_le (n : ℕ) {p : ℝ} (hp : p ∈ Set.Icc 0 1) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k * Real.exp (t * k)) ≤
      Real.exp ((n : ℝ) * p * (Real.exp t - 1)) := by
  rw [binomialMass_mgf]
  have hn : 0 ≤ 1 - p + p * Real.exp t := by positivity [sub_nonneg.mpr hp.2, hp.1]
  have he : 1 - p + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
    nlinarith only [Real.add_one_le_exp (p * (Real.exp t - 1))]
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) ^ n := pow_le_pow_left₀ hn he n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Exponential Markov bound for a finite nonnegative measure. -/
theorem finite_exp_markov {α : Type*} (S : Finset α) (w X : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (a t : ℝ) (ht : 0 ≤ t) :
    (∑ z ∈ S with a ≤ X z, w z) ≤
      Real.exp (-t * a) * ∑ z ∈ S, w z * Real.exp (t * X z) := by
  classical
  calc
    _ = ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * a)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_left_comm, ← Real.exp_add]
      simp
    _ ≤ ∑ z ∈ S with a ≤ X z, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := Finset.mem_filter.mp hz
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h.2 ht)) (hw z h.1))
        (Real.exp_nonneg _)
    _ ≤ ∑ z ∈ S, Real.exp (-t * a) * (w z * Real.exp (t * X z)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro z hz _
      positivity [hw z hz]
    _ = _ := by rw [Finset.mul_sum]

end TraceReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]

theorem sum_pairedHiddenMass (H : FiniteLaw α) (ω : ℝ) :
    (∑ z, pairedHiddenMass H ω z) = ω ^ 2 := by
  unfold pairedHiddenMass
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, H.total, mul_one]
  rw [← Finset.mul_sum, H.total, mul_one]

/-- Forgetting the report recovers conditional independence for each orientation. -/
theorem pairedFlag_simulation (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) (z : α × α) :
    (∑ c : Option Bool, pairedFlagMass P Q H ω b (c, z)) =
      (orientedProd P Q b).mass z := by
  cases b <;> simp [pairedFlagMass, Fintype.sum_option ]

end TraceReconstruction.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parity

Parity-tree roles, forced leaves, coefficient shapes, and exact unsigned/signed motif expansions.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
attribute [local instance] Classical.propDecidable

theorem motif_child_sign {χ σ τ : ℝ} (hm : IsMotifValue χ σ) (ht : IsTypeSign τ) :
    IsTypeSign (1-χ+σ*τ) := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,hσ⟩
  · exact Or.inl (by ring)
  · rcases hσ with rfl | rfl <;> rcases ht with rfl | rfl <;>
      norm_num [IsTypeSign]

end TraceReconstruction


end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Differences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differences

Tensor gap differences, positional shifts, two-gap elimination, central clipping, disjoint rank regions, and weighted period sums.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section



noncomputable section



noncomputable section



noncomputable section


noncomputable section

open Filter
open scoped Topology

noncomputable section
noncomputable section
namespace TraceReconstruction

/-- An elementary centered MGF bound valid on both sides of the mean,
 with constants independent of the Bernoulli parameter. -/
theorem binomialMass_centered_mgf (n : ℕ) {p t : ℝ}
    (hp : p∈Set.Icc 0 1) (ht : |t|≤1) :
    (∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*((k:ℝ)-n*p))) ≤
      Real.exp ((n:ℝ)*t^2) := by
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  have hn : 0≤(n:ℝ)*p := mul_nonneg (Nat.cast_nonneg _) hp.1
  have hn' : (n:ℝ)*p≤n := mul_le_of_le_one_right (Nat.cast_nonneg _) hp.2
  calc
    _ = Real.exp (-t*(n:ℝ)*p)*
        ∑ k∈Finset.range (n+1), binomialMass n p k*Real.exp (t*k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-t*(n:ℝ)*p)*Real.exp ((n:ℝ)*p*(Real.exp t-1)) :=
      mul_le_mul_of_nonneg_left (binomialMass_mgf_le n hp t) (Real.exp_nonneg _)
    _ ≤ Real.exp ((n:ℝ)*t^2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have he' := mul_le_mul_of_nonneg_left he hn
      have hs := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      nlinarith only [he',hs]

end TraceReconstruction
noncomputable section


noncomputable section


noncomputable section


noncomputable section
open scoped Classical


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem prouhet_motif_value (s : ℕ) (z : ℤ) :
    IsMotifValue (motifIndicator s z) ((prouhetSeries s).coeff z) := by
  by_cases hz : 0 ≤ z ∧ z < (2^s : ℕ)
  · right
    refine ⟨by simp only [motifIndicator,ite_eq_left hz], ?_⟩
    have hv := (prouhetSeries_coeff_spec s).2 z hz.1 hz.2
    exact (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hv
  · left
    refine ⟨by simp only [motifIndicator,ite_eq_right hz], ?_⟩
    apply (prouhetSeries_coeff_spec s).1 z
    omega

end TraceReconstruction


noncomputable section


namespace TraceReconstruction

theorem templateType_inside_window {P T a L t : ℕ}
    (sign : Fin L → Bool) (τ : Bool) (hfit : t+T ≤ P)
    (hleft : t ≤ a) (h : Fin T) :
    templateType P a L sign τ (childWindowIndex t hfit h)=
      templateType T (a-t) L sign τ h := by
  have he : (a ≤ (childWindowIndex t hfit h).val ∧
      (childWindowIndex t hfit h).val < a+L) ↔
      a-t ≤ h.val ∧ h.val < a-t+L := by dsimp [childWindowIndex]; omega
  unfold templateType
  split_ifs with h1 h2 h2
  · congr 2
    apply Fin.ext
    dsimp [childWindowIndex]
    omega
  · exact False.elim (h2 (he.mp h1))
  · exact False.elim (h1 (he.mpr h2))
  · rfl

/-- When the motif fits its assigned window, every atom outside that
 window has the default pure type, including pieces crossing nominal cuts. -/
theorem templateType_outside_window {P T a L t : ℕ}
    (sign : Fin L → Bool) (τ : Bool) (hleft : t ≤ a) (hright : a+L ≤ t+T)
    (i : Fin P) (hi : i.val < t ∨ t+T ≤ i.val) :
    templateType P a L sign τ i=false := by
  have he : ¬(a ≤ i.val ∧ i.val < a+L) := by omega
  simp [templateType,he]

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Patterns

Pattern serialization, motif norms, flag posteriors, signed rank coefficients, translated binomials, and support geometry.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


namespace TraceReconstruction

theorem centered_window_floor_fit (P T L t : ℕ) (Y : ℤ)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T)
    (hL : 8*L ≤ T) (hY : |8*Y| ≤ (T:ℤ))
    (ht : (t:ℤ)=(((P-T)/2:ℕ):ℤ)+Y) :
    t+T ≤ P ∧ t ≤ P/2 ∧ P/2+L ≤ t+T := by
  obtain ⟨k,hk⟩ := heven
  have hy := abs_le.mp hY
  omega

theorem centered_window_floor_anchor (P T : ℕ) (hTP : T ≤ P) (heven : Even T) :
    P/2-(P-T)/2=T/2 := by
  obtain ⟨k,hk⟩ := heven
  omega

theorem atomString_append (n m : ℕ) (w : Bool → List Bool) (θ : Fin (n+m) → Bool) :
    atomString (n+m) w θ =
      atomString n w (fun i => θ (i.castLE (Nat.le_add_right n m))) ++
      atomString m w (fun i => θ (i.natAdd n)) := by
  simp only [atomString,List.ofFn_add,List.flatten_append]

theorem atomString_three (n m k : ℕ) (w : Bool → List Bool) (θ : Fin (n+m+k) → Bool) :
    atomString (n+m+k) w θ =
      atomString n w (fun i => θ ⟨i.val,by omega⟩) ++
      atomString m w (fun i => θ ⟨n+i.val,by omega⟩) ++
      atomString k w (fun i => θ ⟨n+m+i.val,by omega⟩) := by
  rw [atomString_append,atomString_append]
  rfl

/-- A full deterministic template equals a pure prefix, the actual translated
 window, and a pure suffix. This equality is in unmarked binary strings. -/
theorem template_word_window (t T z a L : ℕ) (sign : Fin L → Bool) (τ : Bool)
    (w : Bool → List Bool) (hleft : t ≤ a) (hright : a+L ≤ t+T) :
    atomString (t+T+z) w (templateType (t+T+z) a L sign τ) =
      atomString t w (fun _ => false) ++
      atomString T w (templateType T (a-t) L sign τ) ++
      atomString z w (fun _ => false) := by
  rw [atomString_three]
  congr 2
  · congr 1
    funext i
    exact templateType_outside_window sign τ hleft hright ⟨i.val,by omega⟩ (Or.inl i.isLt)
  · congr 1
    funext i
    exact templateType_inside_window sign τ (by omega) hleft i
  · funext i
    exact templateType_outside_window sign τ hleft hright ⟨t+T+i.val,by omega⟩ (Or.inr (by dsimp; omega))

theorem atomString_constant (n : ℕ) (w : Bool → List Bool) (b : Bool) :
    atomString n w (fun _ => b)=pureAtomRun (w b) n := by
  simp [atomString,pureAtomRun]

theorem pureAtomRun_add (w : List Bool) (n m : ℕ) :
    pureAtomRun w (n+m)=pureAtomRun w n ++ pureAtomRun w m := by
  simp only [pureAtomRun,List.replicate_add,List.flatten_append]

/-- Splitting or regrouping a pure region into reported chunks changes no
 unmarked string. In particular arbitrary fixed chunk IDs are harmless. -/
theorem pureAtomRun_partition (w : List Bool) (ns : List ℕ) :
    (ns.map (pureAtomRun w)).flatten=pureAtomRun w ns.sum := by
  induction ns with
  | nil => simp [pureAtomRun]
  | cons n ns ih => simp [ih,pureAtomRun_add]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

/-- Pointwise Bayes factorization, valid even at zero probability reports. -/
theorem pairedFlag_bayes (P Q H : FiniteLaw α) (ω : ℝ)
    (z : Option Bool × (α × α)) (b : Bool) :
    (1/2 : ℝ)*pairedFlagMass P Q H ω b z =
      pairedReportMass P Q H ω z * (flagPosterior z.1).mass b := by
  rcases z with ⟨d,z⟩
  cases d with
  | none => simp [pairedReportMass,pairedFlagMass,flagPosterior]; ring
  | some c => cases b <;> cases c <;>
      simp [pairedReportMass,pairedFlagMass,flagPosterior]

/-- Conditioning solely on exact reports does not correlate mechanisms.
 This is the actual joint-mass factorization, not an independence hypothesis. -/
theorem pairedFlags_product_bayes {ι : Type*} [Fintype ι]
    (P Q H : ι → FiniteLaw α) (ω : ι → ℝ)
    (z : ι → Option Bool × (α × α)) (b : ι → Bool) :
    (∏ i, (1/2 : ℝ)*pairedFlagMass (P i) (Q i) (H i) (ω i) (b i) (z i)) =
      (∏ i, pairedReportMass (P i) (Q i) (H i) (ω i) (z i)) *
        ∏ i, (flagPosterior (z i).1).mass (b i) := by
  simp_rw [pairedFlag_bayes]
  exact Finset.prod_mul_distrib

end TraceReconstruction.FiniteLaw


end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Oracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oracles

TV kernels and trace simulation, anchor costs, counted primitives, common-part lifting, concrete oracle pairs, and paired-flag metadata.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section


noncomputable section
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_comm (P : FiniteLaw α) (Q : FiniteLaw β) (F : α→β→ℝ) :
    P.expect (fun a => Q.expect (F a))=Q.expect (fun b => P.expect (fun a => F a b)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end FiniteLaw

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem coordinateWord_pureAtomRun {n : ℕ} (w : List Bool) (k : Fin n→ℕ) :
    coordinateWord (fun i => pureAtomRun w (k i))=pureAtomRun w (∑i,k i) := by
  change (List.ofFn (pureAtomRun w ∘ k)).flatten=_
  rw [←List.map_ofFn,pureAtomRun_partition,List.sum_ofFn]

end TraceReconstruction
noncomputable section
universe u



/-!
Concrete objects for the scale inequalities, Definition 3 (the level invariant).
The observable channel remains the complete deletion trace of a literal word.
-/
noncomputable section



/-! The actual finite paired-flag experiment.  We separate its unconditional
orientation-first generation (used for trace simulation) from its exact
metadata-first Bayes factorization (used for the density estimates).
Neither construction conditions on successful window layout. -/
noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem expect_joint (P : FiniteLaw α) (K : α → FiniteLaw β) (F : α × β → ℝ) :
    (P.joint K).expect F = P.expect (fun a => (K a).expect (fun b => F (a,b))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_mixture (P : FiniteLaw α) (K : α → FiniteLaw β) (F : β → ℝ) :
    (P.mixture K).expect F = P.expect (fun a => (K a).expect F) := by
  simp only [expect, mixture, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Independent maps commute with the literal finite product law. -/
theorem coordinateProduct_map {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → β) :
    (coordinateProduct P).map (fun a i => f i (a i)) =
      coordinateProduct (fun i => (P i).map (f i)) := by
  apply FiniteLaw.ext
  funext b
  rw [map_mass]
  change (∑ a : Fin n → α, if (fun i => f i (a i)) = b then ∏ i, (P i).mass (a i) else 0) =
    ∏ i, ((P i).map (f i)).mass (b i)
  simp_rw [map_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : (fun i => f i (a i)) = b
  · rw [ite_eq_left hab]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun hab i)]
  · rw [ite_eq_right hab]
    symm
    have hi : ∃ i, f i (a i) ≠ b i := by
      by_contra h
      push Not at h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Forgetting the report recovers the two independent side emissions. -/
theorem pairedFlagLaw_map (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω*H.mass a ≤ P.mass a) (hQ : ∀ a, ω*H.mass a ≤ Q.mass a)
    (b : Bool) :
    (pairedFlagLaw P Q H hω hP hQ b).map Prod.snd = orientedProd P Q b := by
  apply FiniteLaw.ext
  funext z
  rw [map_mass, Fintype.sum_prod_type]
  simp only [pairedFlagLaw]
  simp_rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact pairedFlag_simulation P Q H ω b z

end FiniteLaw

variable {Side Leaf : Type*} [Fintype Side] [Fintype Leaf] {m n : ℕ}

namespace PairedMechanisms
variable (M : PairedMechanisms Side m)

theorem oracle_factorization (P Q : FiniteLaw Leaf) (θ : (Fin m → Bool) → Fin n → Bool) :
    M.orientationOracle P Q θ = M.canonicalOracle P Q θ := by
  apply FiniteLaw.ext
  funext zx
  rcases zx with ⟨z,x⟩
  change (∑ b, (∏ i : Fin m, (1/2:ℝ)) *
      ((∏ i, FiniteLaw.pairedFlagMass (M.first i) (M.second i) (M.common i)
        (M.hiddenWeight i) (b i) (z i)) * (selectedLeafLaw P Q (θ b)).mass x)) =
    (∏ i, FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i)
      (M.hiddenWeight i) (z i)) *
      (∑ b, (∏ i, (FiniteLaw.flagPosterior (z i).1).mass (b i)) * (selectedLeafLaw P Q (θ b)).mass x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc, ← Finset.prod_mul_distrib,
    FiniteLaw.pairedFlags_product_bayes, mul_assoc]

/-- The reference is independent old-first-law emissions, even after reporting
all side traces. This equality is exact for every metadata value. -/
theorem canonicalOracle_density (P Q : FiniteLaw Leaf) (Z : Leaf → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a*(1+Z a))
    (θ : (Fin m → Bool) → Fin n → Bool) (z : Reports Side m) (x : Fin n → Leaf) :
    (M.canonicalOracle P Q θ).mass (z,x) =
      (M.reports.prod (P.product n)).mass (z,x) *
        averagedDensity (orientationsGiven z) θ Z x := by
  change M.reports.mass z *
    ((orientationsGiven z).mixture (fun b => FiniteLaw.coordinateProduct
      (fun i => if θ b i then Q else P))).mass x = _
  rw [leaf_oracle_density P Q Z hZ]
  exact (mul_assoc _ _ _).symm

/-- The full side metadata has a common law for both hypotheses. -/
theorem canonicalOracle_metadata (P Q : FiniteLaw Leaf)
    (θ : (Fin m → Bool) → Fin n → Bool) (F : Reports Side m → ℝ) :
    (M.canonicalOracle P Q θ).expect (fun z => F z.1) = M.reports.expect F := by
  rw [canonicalOracle, FiniteLaw.expect_joint]
  simp only [FiniteLaw.expect_const]

/-- Conditional on every orientation, forgetting flags gives independent side
emissions. This is the unconditional simulation side of the construction. -/
theorem reportsGiven_forget (b : Fin m → Bool) :
    (M.reportsGiven b).map (fun z i => (z i).2) =
      FiniteLaw.coordinateProduct (fun i => FiniteLaw.orientedProd (M.first i) (M.second i) (b i)) := by
  rw [reportsGiven, FiniteLaw.coordinateProduct_map]
  congr 1
  funext i
  exact FiniteLaw.pairedFlagLaw_map _ _ _ _ _ _ _

end PairedMechanisms
end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_LeafOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem motifChildSign_isSign (s : ℕ) (X : ℤ) (h : ℕ) {τ : ℝ} (hτ : IsTypeSign τ) :
    IsTypeSign (motifChildSign s X h τ) :=
  motif_child_sign (prouhet_motif_value s ((h:ℤ)-X)) hτ

end TraceReconstruction


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_const_mul (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f := by
  unfold expect
  simp only [mul_left_comm (P.mass _) c,Finset.mul_sum]

theorem coordinateProduct_expect_product {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i,f i (x i)) = ∏i,(P i).expect (f i) := by
  unfold expect coordinateProduct
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : α) => (P i).mass a*f i a)).symm

end FiniteLaw

end TraceReconstruction

-- Actual subtree coefficient factorization and singleton cancellation.
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw

/-- Unoccupied independent coordinates integrate to one. -/
theorem coordinateProduct_expect_subtype {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (S : Finset (Fin n)) (f : S → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i : S, f i (x i.val)) =
      ∏i : S, (P i.val).expect (f i) := by
  have scalar : ∀f : S → ℝ,
      (∏j : Fin n, if hj : j∈S then f ⟨j,hj⟩ else 1) = ∏i : S,f i := by
    intro f
    calc
      _ = ∏j∈S, if hj : j∈S then f ⟨j,hj⟩ else 1 :=
        (Finset.prod_subset S.subset_univ (fun j _ hj => dite_eq_right hj)).symm
      _ = ∏i : S, if hj : i.val∈S then f ⟨i.val,hj⟩ else 1 :=
        Finset.prod_subtype S (fun _ => Iff.rfl) _
      _ = _ := by simp only [dite_eq_left (Subtype.property _)]
  let F : Fin n → α → ℝ := fun j a => if hj : j∈S then f ⟨j,hj⟩ a else 1
  have hp : ∀x : Fin n → α, (∏j,F j (x j)) = ∏i : S,f i (x i.val) := by
    intro x
    exact scalar (fun i => f i (x i.val))
  rw [show (fun x : Fin n → α => ∏i : S,f i (x i.val)) = (fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm]
  rw [coordinateProduct_expect_product]
  have he : ∀j, (P j).expect (F j) = if hj : j∈S then (P j).expect (f ⟨j,hj⟩) else 1 := by
    intro j
    by_cases hj : j∈S
    · simp only [F,dite_eq_left hj]
    · simp only [F,dite_eq_right hj,expect_const]
  simp_rw [he]
  exact scalar (fun i => (P i.val).expect (f i))

end FiniteLaw


end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy

Shaped envelopes, actual coefficient aggregation, role counts, central contributions, and full coefficient energy.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem sourceNoncentralMass_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    0 ≤ sourceNoncentralMass T n g s center globalShift A b d incoming := by
  exact Finset.sum_nonneg (fun bits _ => mul_nonneg
    ((windowPosteriorLaw T n g b d).nonneg bits) (by dsimp only; split_ifs <;> norm_num))

end TraceReconstruction


end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Layout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Layout

Multiwindow and paired layouts, coordinate simulations, and literal source types and trees.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem framedConcat_succ {α : Type*} (e : α) {k : ℕ}
    (pre post : Fin (k+1) → ℕ) (W : Fin (k+1) → List α) :
    framedConcat e pre post W = List.replicate (pre 0) e ++ W 0 ++
      List.replicate (post 0) e ++
      framedConcat e (fun i => pre i.succ) (fun i => post i.succ) (fun i => W i.succ) := by
  simp [framedConcat,List.ofFn_succ,List.append_assoc]

/-- Only the first, last, and intervening pure lengths are observable in an
unmarked word. In particular boundaries may jitter across nominal units. -/
theorem framedConcat_eq_of_gaps {α : Type*} (e : α) (k : ℕ)
    (pre post pre' post' : Fin (k+1) → ℕ) (W : Fin (k+1) → List α)
    (u u' : ℕ) (hfirst : u+pre 0=u'+pre' 0)
    (hgap : ∀i : Fin k, post i.castSucc+pre i.succ=post' i.castSucc+pre' i.succ)
    (hlast : post (Fin.last k)=post' (Fin.last k)) :
    List.replicate u e ++ framedConcat e pre post W =
      List.replicate u' e ++ framedConcat e pre' post' W := by
  induction k generalizing u u' with
  | zero =>
    have hl : post 0=post' 0 := hlast
    simp only [framedConcat,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,
      List.flatten_nil,List.append_nil]
    calc
      _ = List.replicate (u+pre 0) e ++ W 0 ++ List.replicate (post 0) e := by
        simp only [List.replicate_add,List.append_assoc]
      _ = List.replicate (u'+pre' 0) e ++ W 0 ++ List.replicate (post' 0) e := by rw [hfirst,hl]
      _ = _ := by simp only [List.replicate_add,List.append_assoc]
  | succ k ih =>
    rw [framedConcat_succ e pre post W,framedConcat_succ e pre' post' W]
    have ht := ih (fun i => pre i.succ) (fun i => post i.succ)
      (fun i => pre' i.succ) (fun i => post' i.succ) (fun i => W i.succ)
      (post 0) (post' 0) (hgap 0) (fun i => hgap i.succ) hlast
    calc
      _ = List.replicate (u+pre 0) e ++ W 0 ++
          (List.replicate (post 0) e ++ framedConcat e
            (fun i => pre i.succ) (fun i => post i.succ) (fun i => W i.succ)) := by
        simp only [List.replicate_add,List.append_assoc]
      _ = List.replicate (u'+pre' 0) e ++ W 0 ++
          (List.replicate (post' 0) e ++ framedConcat e
            (fun i => pre' i.succ) (fun i => post' i.succ) (fun i => W i.succ)) := by rw [hfirst,ht]
      _ = _ := by simp only [List.replicate_add,List.append_assoc]

theorem framePrefix_zero {k : ℕ} (pre post len : Fin k → ℕ) :
    framePrefix pre post len 0=0 := by simp [framePrefix]

theorem framePrefix_step {k : ℕ} (pre post len : Fin k → ℕ) (i : Fin k) :
    framePrefix pre post len (i.val+1)=framePrefix pre post len i.val+pre i+len i+post i := by
  have he : (fun j : Fin k => if j.val < i.val+1 then pre j+len j+post j else 0)=
      fun j => (if j.val < i.val then pre j+len j+post j else 0)+
        (if j=i then pre i+len i+post i else 0) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun h' => h (Fin.ext h')
      by_cases hlt : j.val < i.val
      · simp [hlt,show j.val < i.val+1 by omega,h]
      · simp [hlt,show ¬j.val < i.val+1 by omega,h]
  simp only [framePrefix,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  omega

/-- Equal actual starting positions and equal total counts are enough:
there is no requirement that a part coincide with its nominal unit. -/
theorem framedConcat_eq_of_starts {α : Type*} (e : α) (k : ℕ)
    (pre post pre' post' : Fin (k+1) → ℕ) (W : Fin (k+1) → List α)
    (hstart : ∀i : Fin (k+1),
      framePrefix pre post (fun j => (W j).length) i.val+pre i=
      framePrefix pre' post' (fun j => (W j).length) i.val+pre' i)
    (htotal : framePrefix pre post (fun j => (W j).length) (k+1)=
      framePrefix pre' post' (fun j => (W j).length) (k+1)) :
    framedConcat e pre post W=framedConcat e pre' post' W := by
  have H := framedConcat_eq_of_gaps e k pre post pre' post' W 0 0
  simp only [List.replicate_zero,List.nil_append] at H
  apply H
  · simpa only [Fin.val_zero,framePrefix_zero,zero_add] using hstart 0
  · intro i
    have h₁ := hstart i.castSucc
    have h₂ := hstart i.succ
    have h₃ := framePrefix_step pre post (fun j => (W j).length) i.castSucc
    have h₄ := framePrefix_step pre' post' (fun j => (W j).length) i.castSucc
    simp only [Fin.val_castSucc,Fin.val_succ] at *
    omega
  · have h₁ := hstart (Fin.last k)
    have h₂ := framePrefix_step pre post (fun j => (W j).length) (Fin.last k)
    have h₃ := framePrefix_step pre' post' (fun j => (W j).length) (Fin.last k)
    simp only [Fin.val_last] at *
    omega

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem framePrefix_constant {k : ℕ} (pre post len : Fin k → ℕ) (P i : ℕ)
    (hc : ∀j,pre j+len j+post j=P) (hi : i ≤ k) :
    framePrefix pre post len i=i*P := by
  induction i with
  | zero => simp [framePrefix_zero]
  | succ i ih =>
    have h := framePrefix_step pre post len ⟨i,by omega⟩
    have hh := hc ⟨i,by omega⟩
    rw [h,ih (by omega),Nat.add_mul,Nat.one_mul]
    omega

theorem flatten_framedConcat (w : List Bool) {k : ℕ}
    (pre post : Fin k → ℕ) (W : Fin k → List (List Bool)) :
    (framedConcat w pre post W).flatten=
      (List.ofFn (fun i => pureAtomRun w (pre i) ++ (W i).flatten ++
        pureAtomRun w (post i))).flatten := by
  rw [framedConcat,List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp [Function.comp_apply,List.flatten_append,pureAtomRun]

/-- The deterministic multiwindow identity used by the nested simulator.
Every motif is covered by its own window. Predetermined pure-region lengths
may move the boundaries of nominal units; only their exact cumulative counts
are required. Windows and chunks all remain literal unmarked binary words. -/
theorem template_group_windows (k P T a L : ℕ) (sign : Fin L → Bool)
    (w : Bool → List Bool) (τ : Fin (k+1) → Bool)
    (t pre post : Fin (k+1) → ℕ)
    (hleft : ∀u,t u ≤ a) (hfit : ∀u,a+L ≤ t u+T)
    (hunit : ∀u,t u+T ≤ P)
    (hstart : ∀u,framePrefix pre post (fun _ => T) u.val+pre u=u.val*P+t u)
    (htotal : framePrefix pre post (fun _ => T) (k+1)=(k+1)*P) :
    (List.ofFn (fun u => complementaryWords P a L sign w (τ u))).flatten=
      (List.ofFn (fun u => pureAtomRun (w false) (pre u) ++
        complementaryWords T (a-t u) L sign w (τ u) ++
        pureAtomRun (w false) (post u))).flatten := by
  let W : Fin (k+1) → List (List Bool) := fun u =>
    List.ofFn (fun i => w (templateType T (a-t u) L sign (τ u) i))
  let z : Fin (k+1) → ℕ := fun u => P-(t u+T)
  have hz : ∀u,t u+T+z u=P := by intro u; dsimp [z]; have hu := hunit u; omega
  have hlen : ∀u,(W u).length=T := by intro u; simp [W]
  have hp : ∀i,i ≤ k+1 → framePrefix t z (fun u => (W u).length) i=i*P :=
    fun i hi => framePrefix_constant t z _ P i (fun u => by rw [hlen]; exact hz u) hi
  have he := framedConcat_eq_of_starts (w false) k t z pre post W
    (fun u => by simp only [hlen] at hp ⊢; rw [hp _ (by omega),hstart])
    (by simp only [hlen] at hp ⊢; rw [hp _ le_rfl,htotal])
  have he' := congrArg List.flatten he
  rw [flatten_framedConcat,flatten_framedConcat] at he'
  calc
    _ = (List.ofFn (fun u => pureAtomRun (w false) (t u) ++ (W u).flatten ++
          pureAtomRun (w false) (z u))).flatten := by
      congr 1
      apply congrArg List.ofFn
      funext u
      have hh := template_word_window (t u) T (z u) a L sign (τ u) w (hleft u) (hfit u)
      rw [hz] at hh
      simpa only [complementaryWords,atomString_constant,W,atomString,List.ofFn_const,pureAtomRun] using hh
    _ = _ := he'

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

theorem pairedPreCount_cast {N : ℕ} (left : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (A : ℕ)
    (hfill : ∀u,filler u+(∑v,if left v=u then reserve v else 0)=A) (u : Fin N) :
    (pairedPreCount left filler first u : ℤ) = A+
      ∑v, if left v=u then (first v:ℤ)-reserve v else 0 := by
  have hf : (filler u:ℤ)+(∑v,if left v=u then (reserve v:ℤ) else 0)=A := by
    exact_mod_cast hfill u
  have he : (∑v,if left v=u then (first v:ℤ)-reserve v else 0)=
      (∑v,if left v=u then (first v:ℤ) else 0)-
        (∑v,if left v=u then (reserve v:ℤ) else 0) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  simp only [pairedPreCount,Nat.cast_add,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [he]
  omega

theorem pairedPostCount_cast {N : ℕ} (right : K → Fin N) (filler : Fin N → ℕ)
    (reserve first : K → ℕ) (A : ℕ) (hfirst : ∀v,first v ≤ 2*reserve v)
    (hfill : ∀u,filler u+(∑v,if right v=u then reserve v else 0)=A) (u : Fin N) :
    (pairedPostCount right filler reserve first u : ℤ) = A-
      ∑v, if right v=u then (first v:ℤ)-reserve v else 0 := by
  have hf : (filler u:ℤ)+(∑v,if right v=u then (reserve v:ℤ) else 0)=A := by
    exact_mod_cast hfill u
  have he : (∑v,if right v=u then ((2*reserve v-first v:ℕ):ℤ) else 0)=
      (∑v,if right v=u then (reserve v:ℤ) else 0)-
        (∑v,if right v=u then (first v:ℤ)-reserve v else 0) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.cast_sub (hfirst v)]
    push_cast
    split_ifs <;> ring
  simp only [pairedPostCount,Nat.cast_add,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
  rw [he]
  omega

/-- Prefix sum of a delta at a prescribed label, with no loss from replacing
 its real finite support by an interval. -/
theorem fin_prefix_delta {N : ℕ} (a : Fin N) (i : ℕ) (x : ℤ) :
    (∑u : Fin N, if u.val < i then (if a=u then x else 0) else 0)=
      if a.val < i then x else 0 := by
  have he : (fun u : Fin N => if u.val < i then (if a=u then x else 0) else 0)=
      fun u => if u=a then (if a.val < i then x else 0) else 0 := by
    funext u
    by_cases h : u=a
    · subst u; simp
    · simp [h,Ne.symm h]
  rw [he]
  simp

/-- Exact paired-interval contribution to the position of a window. -/
theorem pair_activity_identity {N : ℕ} (l r u : Fin N) (hlr : l.val ≤ r.val) (x : ℤ) :
    (if l.val < u.val then x else 0)-(if r.val < u.val then x else 0)+
      (if l=u then x else 0) =
      if l.val ≤ u.val ∧ u.val ≤ r.val then x else 0 := by
  by_cases hlu : l.val < u.val
  · by_cases hru : r.val < u.val
    · simp [hlu,hru,show l≠u by intro h; subst u; omega,show ¬u.val ≤ r.val by omega]
    · simp [hlu,hru,show l≠u by intro h; subst u; omega,show l.val ≤ u.val by omega,show u.val ≤ r.val by omega]
  · by_cases hlu' : l=u
    · subst u; simp [hlr,show ¬r.val < l.val by omega]
    · have hn : l.val≠u.val := fun h => hlu' (Fin.ext h)
      simp [hlu,hlu',show ¬r.val < u.val by omega,show ¬l.val ≤ u.val by omega]

/-- Cumulative pure chunk counts have exactly the source's localBits-plus-active-
globalBits jitter. This identity uses the actual chronological pre/post schedule. -/
theorem pairedLayout_start {N : ℕ} (left right : K → Fin N)
    (horder : ∀v,(left v).val ≤ (right v).val)
    (fpre fpost : Fin N → ℕ) (reserve first : K → ℕ)
    (hfirst : ∀v,first v ≤ 2*reserve v) (A B T : ℕ)
    (hpre : ∀u,fpre u+(∑v,if left v=u then reserve v else 0)=A)
    (hpost : ∀u,fpost u+(∑v,if right v=u then reserve v else 0)=B)
    (u : Fin N) :
    ((framePrefix (pairedPreCount left fpre first)
      (pairedPostCount right fpost reserve first) (fun _ => T) u.val+
      pairedPreCount left fpre first u : ℕ):ℤ)=
      u.val*(A+T+B)+A+
        ∑v, if (left v).val ≤ u.val ∧ u.val ≤ (right v).val then
          (first v:ℤ)-reserve v else 0 := by
  let d : K → ℤ := fun v => (first v:ℤ)-reserve v
  have hpr := pairedPreCount_cast left fpre reserve first A hpre
  have hpo := pairedPostCount_cast right fpost reserve first B hfirst hpost
  have hsum : (∑j : Fin N, if j.val < u.val then (1:ℤ) else 0)=(u.val:ℤ) := by
    have hc := framePrefix_constant (fun _ : Fin N => 0) (fun _ => 0) (fun _ => 1) 1 u.val
      (by simp) (by omega)
    simpa [framePrefix] using congrArg (fun n : ℕ => (n:ℤ)) hc
  simp only [Nat.cast_add,framePrefix,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,hpr,hpo]
  have hex : (∑j : Fin N,if j.val < u.val then
        (A+(∑v,if left v=j then d v else 0))+T+
        (B-(∑v,if right v=j then d v else 0)) else 0)=
      (u.val:ℤ)*(A+T+B)+
        ∑v,((if (left v).val < u.val then d v else 0)-
          (if (right v).val < u.val then d v else 0)) := by
    calc
      _ = (∑j : Fin N,(if j.val < u.val then (1:ℤ) else 0)*(A+T+B))+
          ∑j : Fin N,∑v,
            ((if j.val < u.val then (if left v=j then d v else 0) else 0)-
             (if j.val < u.val then (if right v=j then d v else 0) else 0)) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val < u.val
        · simp [hj,Finset.sum_sub_distrib]; ring
        · simp [hj]
      _ = _ := by
        rw [←Finset.sum_mul,hsum,Finset.sum_comm]
        simp_rw [Finset.sum_sub_distrib,fin_prefix_delta]
  change (∑j : Fin N,if j.val < u.val then
      (A+(∑v,if left v=j then d v else 0))+T+
      (B-(∑v,if right v=j then d v else 0)) else 0)+
      (A+∑v,if left v=u then d v else 0)=_
  rw [hex]
  have he : (∑v,((if (left v).val < u.val then d v else 0)-
      (if (right v).val < u.val then d v else 0)))+
      (∑v,if left v=u then d v else 0)=
      ∑v,if (left v).val ≤ u.val ∧ u.val ≤ (right v).val then d v else 0 := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => pair_activity_identity (left v) (right v) u (horder v) (d v))
  dsimp only [d] at *
  linarith only [he]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
variable {K : Type*} [Fintype K]

theorem pairedLayout_total {N : ℕ} (left right : K → Fin N)
    (fpre fpost : Fin N → ℕ) (reserve first : K → ℕ)
    (hfirst : ∀v,first v ≤ 2*reserve v) (A B T : ℕ)
    (hpre : ∀u,fpre u+(∑v,if left v=u then reserve v else 0)=A)
    (hpost : ∀u,fpost u+(∑v,if right v=u then reserve v else 0)=B) :
    framePrefix (pairedPreCount left fpre first)
      (pairedPostCount right fpost reserve first) (fun _ => T) N=N*(A+T+B) := by
  have hpr := pairedPreCount_cast left fpre reserve first A hpre
  have hpo := pairedPostCount_cast right fpost reserve first B hfirst hpost
  have he : ∀f : K → Fin N,
      (∑u : Fin N,∑v,if f v=u then (first v:ℤ)-reserve v else 0)=
        ∑v,((first v:ℤ)-reserve v) := by
    intro f
    rw [Finset.sum_comm]
    simp
  apply Nat.cast_injective (R:=ℤ)
  simp only [framePrefix,Fin.isLt,ite_true,Nat.cast_sum,Nat.cast_add,hpr,hpo,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
  push_cast
  ring

theorem sourceBundle_order (N : ℕ) (v : SourceBundle N) :
    (sourceBundleLeft N v).val ≤ (sourceBundleRight N v).val := by
  cases v with
  | inl u => rfl
  | inr v => dsimp [sourceBundleLeft,sourceBundleRight]; have := v.isLt; omega

theorem sum_injective_delta_le {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (u : β) (R : ℕ) :
    (∑v,if f v=u then R else 0) ≤ R := by
  by_cases h : ∃v,f v=u
  · obtain ⟨v,hv⟩ := h
    have he : ∀j,f j=u ↔ j=v := fun j => by rw [←hv]; exact hf.eq_iff
    simp [he]
  · push Not at h
    simp [h]

theorem sourceBundle_reserve_pre (N R : ℕ) (u : Fin N) :
    (∑v : SourceBundle N,if sourceBundleLeft N v=u then R else 0) ≤ 2*R := by
  rw [Fintype.sum_sum_type]
  change (∑v : Fin N, if v=u then R else 0)+(∑v : Fin (N/4),
    if (⟨v.val,by have := v.isLt; omega⟩ : Fin N)=u then R else 0) ≤ 2*R
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have h := sum_injective_delta_le
    (fun v : Fin (N/4) => (⟨v.val,by have := v.isLt; omega⟩ : Fin N))
    (fun _ _ he => Fin.ext (congrArg (fun z : Fin N => z.val) he)) u R
  omega

theorem sourceBundle_reserve_post (N R : ℕ) (u : Fin N) :
    (∑v : SourceBundle N,if sourceBundleRight N v=u then R else 0) ≤ 2*R := by
  rw [Fintype.sum_sum_type]
  change (∑v : Fin N, if v=u then R else 0)+(∑v : Fin (N/4),
    if (⟨N-1-v.val,by have := v.isLt; omega⟩ : Fin N)=u then R else 0) ≤ 2*R
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hinj : Function.Injective (fun v : Fin (N/4) =>
      (⟨N-1-v.val,by have := v.isLt; omega⟩ : Fin N)) := by
    intro v w he
    have hv := v.isLt
    have hw := w.isLt
    have h := congrArg Fin.val he
    apply Fin.ext
    dsimp only at h
    omega
  have h := sum_injective_delta_le _ hinj u R
  omega

theorem sourceBundleCount_le (N t h : ℕ) (ht : Even t)
    (localBits : Fin N → Fin t → Bool) (globalBits : Fin ((N/4)*t) → Bool)
    (v : SourceBundle N) : sourceBundleCount N t h localBits globalBits v ≤ 2*(t*h+t/2) := by
  have hh : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hs (b : Fin t → Bool) : (∑a,bitIndex (b a)) ≤ t := by
    calc
      _ ≤ ∑_a : Fin t,1 := Finset.sum_le_sum (fun a _ => by cases b a <;> norm_num [bitIndex])
      _ = t := by simp
  cases v with
  | inl u => dsimp [sourceBundleCount]; have := hs (localBits u); omega
  | inr v => dsimp [sourceBundleCount]; have := hs (fun a => globalBits (globalTrialIndex N t v a)); omega

/-- The actual scheduled bits give precisely the arithmetic source displacement
 Y=H+V, including its common-globalBits plateau and outer-quarter behavior. -/
theorem sourceBundle_activity (N t h : ℕ)
    (localBits : Fin N → Fin t → Bool) (globalBits : Fin ((N/4)*t) → Bool) (u : Fin N) :
    (∑v : SourceBundle N, if (sourceBundleLeft N v).val ≤ u.val ∧
        u.val ≤ (sourceBundleRight N v).val then
      (sourceBundleCount N t h localBits globalBits v:ℤ)-(t*h+t/2:ℕ) else 0)=
      ((∑a : Fin t,(bitIndex (localBits u a):ℤ))-(t/2:ℕ))+
        scheduledGlobalShift N t globalBits u := by
  rw [Fintype.sum_sum_type]
  have he : (∑v : Fin N, if v.val ≤ u.val ∧ u.val ≤ v.val then
      (sourceBundleCount N t h localBits globalBits (.inl v):ℤ)-(t*h+t/2:ℕ) else 0)=
      (∑a : Fin t,(bitIndex (localBits u a):ℤ))-(t/2:ℕ) := by
    have hc : ∀v : Fin N,(v.val ≤ u.val ∧ u.val ≤ v.val) ↔ v=u := by
      intro v
      constructor
      · intro hv; exact Fin.ext (le_antisymm hv.1 hv.2)
      · intro hv; subst v; exact ⟨le_rfl,le_rfl⟩
    simp only [hc,Finset.sum_ite_eq',Finset.mem_univ,ite_true,sourceBundleCount,
      Nat.cast_add,Nat.cast_mul,Nat.cast_sum]
    ring
  change (∑v : Fin N, if v.val ≤ u.val ∧ u.val ≤ v.val then
      (sourceBundleCount N t h localBits globalBits (.inl v):ℤ)-(t*h+t/2:ℕ) else 0)+_=_
  rw [he]
  congr 1
  unfold scheduledGlobalShift
  apply Finset.sum_congr rfl
  intro v _
  have hv := v.isLt
  have hu := u.isLt
  have hc : (sourceBundleLeft N (.inr v)).val ≤ u.val ∧
      u.val ≤ (sourceBundleRight N (.inr v)).val ↔ v.val ≤ u.val ∧ u.val+v.val < N := by
    dsimp [sourceBundleLeft,sourceBundleRight]; omega
  simp only [hc]
  split_ifs
  · simp only [sourceBundleCount,Nat.cast_add,Nat.cast_mul,Nat.cast_sum]; ring
  · rfl

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourcePreFiller_nominal (N A t h : ℕ)
    (hA : 2*sourceLayoutReserve t h ≤ A) (u : Fin N) :
    sourcePreFiller N A t h u+
      (∑v : SourceBundle N,if sourceBundleLeft N v=u then sourceLayoutReserve t h else 0)=A := by
  exact Nat.sub_add_cancel ((sourceBundle_reserve_pre N _ u).trans hA)

theorem sourcePostFiller_nominal (N B t h : ℕ)
    (hB : 2*sourceLayoutReserve t h ≤ B) (u : Fin N) :
    sourcePostFiller N B t h u+
      (∑v : SourceBundle N,if sourceBundleRight N v=u then sourceLayoutReserve t h else 0)=B := by
  exact Nat.sub_add_cancel ((sourceBundle_reserve_post N _ u).trans hB)

theorem sourceLayout_exact_start (N A T B t h : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    ((framePrefix (sourcePreCount N A t h loc glob) (sourcePostCount N B t h loc glob)
      (fun _ => T) u.val+sourcePreCount N A t h loc glob u:ℕ):ℤ)=
      u.val*(A+T+B)+A+sourceDisplacement N t loc glob u := by
  have H := pairedLayout_start (sourceBundleLeft N) (sourceBundleRight N)
    (sourceBundle_order N) (sourcePreFiller N A t h) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)
    (sourceBundleCount_le N t h ht loc glob) A B T
    (sourcePreFiller_nominal N A t h hA) (sourcePostFiller_nominal N B t h hB) u
  simp only [sourceLayoutReserve] at H
  rw [sourceBundle_activity] at H
  exact H

theorem sourceLayout_exact_total (N A T B t h : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool) :
    framePrefix (sourcePreCount N A t h loc glob) (sourcePostCount N B t h loc glob)
      (fun _ => T) N=N*(A+T+B) := by
  exact pairedLayout_total (sourceBundleLeft N) (sourceBundleRight N)
    (sourcePreFiller N A t h) (sourcePostFiller N B t h)
    (fun _ => sourceLayoutReserve t h) (sourceBundleCount N t h loc glob)
    (sourceBundleCount_le N t h ht loc glob) A B T
    (sourcePreFiller_nominal N A t h hA) (sourcePostFiller_nominal N B t h hB)

/-- The literal surrogate side chunks, after concatenation, are a correct
 partition of the actual parent word whenever the windows fit. This is
 an equality of unmarked binary strings, not an assumed channel identity. -/
theorem sourceLayout_literal_partition (k A T B t h a L : ℕ) (ht : Even t)
    (hA : 2*sourceLayoutReserve t h ≤ A) (hB : 2*sourceLayoutReserve t h ≤ B)
    (loc : Fin (k+1) → Fin t → Bool) (glob : Fin (((k+1)/4)*t) → Bool)
    (sign : Fin L → Bool) (w : Bool → List Bool) (τ : Fin (k+1) → Bool)
    (hzero : ∀u,0 ≤ (A:ℤ)+sourceDisplacement (k+1) t loc glob u)
    (hleft : ∀u,sourceWindowStart (k+1) A t loc glob u ≤ a)
    (hfit : ∀u,a+L ≤ sourceWindowStart (k+1) A t loc glob u+T)
    (hunit : ∀u,sourceWindowStart (k+1) A t loc glob u+T ≤ A+T+B) :
    (List.ofFn (fun u => complementaryWords (A+T+B) a L sign w (τ u))).flatten=
      (List.ofFn (fun u => pureAtomRun (w false) (sourcePreCount (k+1) A t h loc glob u) ++
        complementaryWords T (a-sourceWindowStart (k+1) A t loc glob u) L sign w (τ u) ++
        pureAtomRun (w false) (sourcePostCount (k+1) B t h loc glob u))).flatten := by
  apply template_group_windows k (A+T+B) T a L sign w τ
    (sourceWindowStart (k+1) A t loc glob)
    (sourcePreCount (k+1) A t h loc glob) (sourcePostCount (k+1) B t h loc glob)
    hleft hfit hunit
  · intro u
    apply Nat.cast_injective (R:=ℤ)
    rw [sourceLayout_exact_start (k+1) A T B t h ht hA hB]
    simp only [Nat.cast_add,Nat.cast_mul,sourceWindowStart,Int.toNat_of_nonneg (hzero u)]
    ring
  · exact sourceLayout_exact_total (k+1) A T B t h ht hA hB loc glob

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

namespace FiniteLaw
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

/-- Reorder independent emissions by the literal chronological slot order.
The order is a bijection, so no output is duplicated or silently discarded. -/
theorem indexedProduct_expect_equiv (P : ι → FiniteLaw α) (e : κ ≃ ι)
    (F : (ι → α) → ℝ) :
    (indexedProduct P).expect F=(indexedProduct (fun j => P (e j))).expect
      (fun x => F (fun i => x (e.symm i))) := by
  let E : (κ → α) ≃ (ι → α) :=
    { toFun := fun x i => x (e.symm i)
      invFun := fun x j => x (e j)
      left_inv := fun x => by funext j; simp
      right_inv := fun x => by funext i; simp }
  unfold expect indexedProduct
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏i,(P i).mass (x (e.symm i)))*F (fun i => x (e.symm i))=_
  congr 1
  rw [←e.prod_comp]
  simp only [Equiv.symm_apply_apply]

end FiniteLaw

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem boolTypeSign_injective : Function.Injective boolTypeSign := by
  intro a b h
  cases a <;> cases b <;> norm_num [boolTypeSign] at *

theorem boolTypeSign_template (s P a : ℕ) (τ : Bool) (i : Fin P) :
    boolTypeSign (templateType P a (2^s) (prouhetBool s) τ i)=
      motifChildSign s (a:ℤ) i.val (boolTypeSign τ) := by
  by_cases hi : a ≤ i.val ∧ i.val < a+2^s
  · have hz : 0 ≤ (i.val:ℤ)-a ∧ (i.val:ℤ)-a < (2^s:ℕ) := by omega
    have he : ((i.val-a:ℕ):ℤ)=(i.val:ℤ)-a := by omega
    have hc := (abs_eq (by norm_num : (0:ℝ)≤1)).mp
      ((prouhetSeries_coeff_spec s).2 _ hz.1 hz.2)
    have hχ : motifIndicator s ((i.val:ℤ)-a)=1 := by simp only [motifIndicator,ite_eq_left hz]
    rcases hc with hc | hc <;> cases τ <;>
      norm_num [templateType,hi,prouhetBool,he,boolTypeSign,motifChildSign,hχ,hc]
  · have hz : ¬(0 ≤ (i.val:ℤ)-a ∧ (i.val:ℤ)-a < (2^s:ℕ)) := by omega
    have hc : (prouhetSeries s).coeff ((i.val:ℤ)-a)=0 :=
      (prouhetSeries_coeff_spec s).1 _ (by omega)
    have hχ : motifIndicator s ((i.val:ℤ)-a)=0 := by simp only [motifIndicator,ite_eq_right hz]
    simp [templateType,hi,boolTypeSign,motifChildSign,hχ,hc]

theorem sourceWindowStart_cast_of_fit (N P T t : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (u : Fin N)
    (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    (sourceWindowStart N ((P-T)/2) t loc glob u:ℤ)=
      (((P-T)/2:ℕ):ℤ)+sourceDisplacement N t loc glob u := by
  apply Int.toNat_of_nonneg
  have hy := abs_le.mp hY
  omega

/-- A zero-based centered version of the floor-fit calculation. -/
theorem sourceWindowStart_fit (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    sourceWindowStart N ((P-T)/2) t loc glob u+T ≤ P ∧
    sourceWindowStart N ((P-T)/2) t loc glob u ≤ P/2 ∧
    P/2+L ≤ sourceWindowStart N ((P-T)/2) t loc glob u+T :=
  centered_window_floor_fit P T L _ _ hP hT heven hL hY
    (sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY)

/-- The zero-based centered translated anchor, including both half-trial corrections. -/
theorem sourceWindowStart_anchor (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    ((P/2-sourceWindowStart N ((P-T)/2) t loc glob u:ℕ):ℤ)=
      (T/2:ℕ)+(t/2:ℕ)-(∑a : Fin t,(bitIndex (loc u a):ℤ))-
        scheduledGlobalShift N t glob u := by
  have hfit := sourceWindowStart_fit N P T t L loc glob hP hT heven hL u hY
  have hc := sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY
  have ha := centered_window_floor_anchor P T (by omega) heven
  have hA : (P-T)/2 ≤ P/2 := Nat.div_le_div_right (Nat.sub_le P T)
  have ha' : ((P/2:ℕ):ℤ)-((P-T)/2:ℕ)=(T/2:ℕ) := by omega
  rw [Nat.cast_sub hfit.2.1,hc]
  dsimp only [sourceDisplacement]
  linarith only [ha']

/-- The manuscript numbers motif slots from one. Thus its actual zero-based
 onset is P/2-1, not P/2. The strict margins include this endpoint correction. -/
theorem sourceWindowStart_oneBased_fit (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    sourceWindowStart N ((P-T)/2) t loc glob u+T ≤ P ∧
    sourceWindowStart N ((P-T)/2) t loc glob u ≤ P/2-1 ∧
    P/2-1+L ≤ sourceWindowStart N ((P-T)/2) t loc glob u+T := by
  have hc := sourceWindowStart_cast_of_fit N P T t loc glob hP hT u hY
  have ha := centered_window_floor_anchor P T (by omega) heven
  have hy := abs_le.mp hY
  omega

/-- The exact source anchor in zero-based coordinates. The minus one is
 forced by the one-based motif-label convention. -/
theorem sourceWindowStart_oneBased_anchor (N P T t L : ℕ)
    (loc : Fin N → Fin t → Bool) (glob : Fin ((N/4)*t) → Bool)
    (hP : 2*T ≤ P) (hT : 16 ≤ T) (heven : Even T) (hL : 8*L ≤ T)
    (u : Fin N) (hY : |8*sourceDisplacement N t loc glob u| ≤ (T:ℤ)) :
    ((P/2-1-sourceWindowStart N ((P-T)/2) t loc glob u:ℕ):ℤ)=
      (T/2:ℕ)-1+(t/2:ℕ)-(∑a : Fin t,(bitIndex (loc u a):ℤ))-
        scheduledGlobalShift N t glob u := by
  have hf := sourceWindowStart_oneBased_fit N P T t L loc glob hP hT heven hL u hY
  have ha := sourceWindowStart_anchor N P T t L loc glob hP hT heven hL u hY
  omega

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem boolTypeSign_integerTemplate (N s : ℕ) (X : ℤ) (τ : Bool) (u : Fin N) :
    boolTypeSign (integerTemplateType N s X τ u)=motifChildSign s X u.val (boolTypeSign τ) := by
  have hτ : IsTypeSign (boolTypeSign τ) := by cases τ <;> norm_num [IsTypeSign,boolTypeSign]
  rcases motifChildSign_isSign s X u.val hτ with h | h <;>
    (simp only [integerTemplateType,h]; norm_num [boolTypeSign])

theorem integerTemplateType_nat (N s a : ℕ) (τ : Bool) :
    integerTemplateType N s (a:ℤ) τ=templateType N a (2^s) (prouhetBool s) τ := by
  funext u
  apply boolTypeSign_injective
  rw [boolTypeSign_integerTemplate,boolTypeSign_template]

theorem sourceNominal_total (P T : ℕ → ℕ) (b : ℕ) (h : T b ≤ P b) :
    sourceNominalPre P T b+T b+sourceNominalPost P T b=P b := by
  dsimp [sourceNominalPre,sourceNominalPost]
  omega

theorem SourceLayoutMargins.restrict {s : ℕ} {P T n h : ℕ → ℕ} {b c : ℕ}
    (H : SourceLayoutMargins s P T n h b) (hc : c≤b) : SourceLayoutMargins s P T n h c := by
  constructor <;> intro j hj
  · exact H.positive j (lt_of_lt_of_le hj hc)
  · exact H.large j (lt_of_lt_of_le hj hc)
  · exact H.even_window j (lt_of_lt_of_le hj hc)
  · exact H.ambient j (lt_of_lt_of_le hj hc)
  · exact H.motif j (lt_of_lt_of_le hj hc)
  · exact H.even_trials j (lt_of_lt_of_le hj hc)
  · exact H.pre_reserve j (lt_of_lt_of_le hj hc)
  · exact H.post_reserve j (lt_of_lt_of_le hj hc)

end TraceReconstruction

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Metadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Metadata

Hidden metadata, fair jitter, heterogeneous emissions, independent window trials, concentration, and fit.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem pairedReportMass_none (P Q H : FiniteLaw α) (ω : ℝ) (z : α × α) :
    pairedReportMass P Q H ω (none,z)=pairedHiddenMass H ω z := by
  simp only [pairedReportMass,Fintype.sum_bool,pairedFlagMass]
  ring

theorem pairedReport_hidden_expect (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a) (F : ℕ → ℝ) :
    (pairedReport P Q H hω hP hQ).expect (fun z => F (hiddenTrial z.1))=
      ω^2*F 1+(1-ω^2)*F 0 := by
  let R := pairedReport P Q H hω hP hQ
  have hp : R.expect (fun z => if z.1=none then (1:ℝ) else 0)=ω^2 := by
    simp only [expect,R,pairedReport,Fintype.sum_prod_type,Fintype.sum_option]
    simp only [reduceCtorEq,ite_false,mul_zero,Finset.sum_const_zero,add_zero]
    simpa only [pairedReportMass_none,Fintype.sum_prod_type,ite_true,mul_one] using sum_pairedHiddenMass H ω
  have he (z : Option Bool × (α × α)) : F (hiddenTrial z.1)=
      F 0+(F 1-F 0)*(if z.1=none then 1 else 0) := by
    rcases z with ⟨d,z⟩; cases d <;> simp [hiddenTrial]
  simp_rw [he]
  have hadd : R.expect (fun z => F 0+(F 1-F 0)*(if z.1=none then 1 else 0))=
      R.expect (fun _ => F 0)+R.expect (fun z => (F 1-F 0)*(if z.1=none then 1 else 0)) := by
    simp only [expect,mul_add,Finset.sum_add_distrib]
  rw [hadd,expect_const,expect_const_mul,hp]
  ring

/-- Centered hidden-flag MGF, derived from the literal paired experiment. -/
theorem pairedReport_hidden_mgf (P Q H : FiniteLaw α) {ω t : ℝ} (hω : 0≤ω)
    (hP : ∀a,ω*H.mass a≤P.mass a) (hQ : ∀a,ω*H.mass a≤Q.mass a)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    (pairedReport P Q H hω hP hQ).expect (fun z =>
      Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2)))≤Real.exp (t^2) := by
  rw [pairedReport_hidden_expect P Q H hω hP hQ (fun k => Real.exp (t*((k:ℝ)-ω^2)))]
  have H := binomialMass_centered_mgf 1 hp ht
  norm_num [Finset.sum_range_succ,binomialMass] at H ⊢
  convert H using 1 <;> first | rfl | ring

end FiniteLaw

namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

/-- Exact Bayes averaging under all metadata, including impossible reports. -/
theorem posterior_average (F : (Fin m → Bool) → ℝ) :
    M.reports.expect (fun z => (orientationsGiven z).expect F)=
      (fairOrientations m).expect F := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hb (z : Reports Side m) : M.reports.mass z*(orientationsGiven z).mass b=
      (fairOrientations m).mass b*(M.reportsGiven b).mass z := by
    change (∏i,FiniteLaw.pairedReportMass (M.first i) (M.second i) (M.common i) (M.hiddenWeight i) (z i))*
      (∏i,(FiniteLaw.flagPosterior (z i).1).mass (b i))=_
    rw [←FiniteLaw.pairedFlags_product_bayes]
    rw [Finset.prod_mul_distrib]
    rfl
  simp_rw [←mul_assoc,hb,mul_assoc]
  rw [←Finset.mul_sum,←Finset.sum_mul,(M.reportsGiven b).total,one_mul]

end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem indexedProduct_expect_product (P : ι → FiniteLaw α) (F : ι → α → ℝ) :
    (indexedProduct P).expect (fun x => ∏i,F i (x i))=∏i,(P i).expect (F i) := by
  simp only [expect,indexedProduct,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).mass a*F i a)).symm

end FiniteLaw

/-- Exact MGF calculation for each paired orientation bit. -/
theorem fairBit_mgf (t : ℝ) :
    (FiniteLaw.flagPosterior none).expect (fun b => Real.exp (t*((bitIndex b:ℝ)-1/2)))=
      Real.cosh (t/2) := by
  simp only [FiniteLaw.expect,Fintype.sum_bool,FiniteLaw.flagPosterior,bitIndex]
  norm_num only [Bool.false_eq_true,↓reduceIte,Nat.cast_zero,Nat.cast_one,decide_true,decide_false,if_true,if_false]
  rw [Real.cosh_eq]
  ring_nf

/-- Hoeffding's exponential estimate for the actual independently fair bits,
 allowing deterministic zero coefficients for completed/nonactive global pairs. -/
theorem fairLinearSum_mgf {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ℝ) :
    (fairField ι).expect (fun bits => Real.exp (t*fairLinearSum c bits))≤
      Real.exp ((∑i,(c i)^2)*t^2/8) := by
  have he (bits : ι → Bool) : Real.exp (t*fairLinearSum c bits)=
      ∏i,Real.exp ((t*c i)*((bitIndex (bits i):ℝ)-1/2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [fairLinearSum,Finset.mul_sum,mul_assoc]
  simp_rw [he]
  rw [fairField,FiniteLaw.indexedProduct_expect_product _
    (fun i b => Real.exp ((t*c i)*((bitIndex b:ℝ)-1/2)))]
  simp_rw [fairBit_mgf]
  calc
    _ ≤ ∏i,Real.exp ((t*c i)^2/8) := by
      apply Finset.prod_le_prod
      · intro i _; exact (Real.cosh_pos _).le
      · intro i _
        convert Real.cosh_le_exp_half_sq (t*c i/2) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ring
    _ = _ := by
      rw [←Real.exp_sum]
      congr 1
      simp only [Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Two-sided finite Hoeffding bound with the source's sharp quadratic scale. -/
theorem fairLinearSum_tail_variance {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {V : ℝ} (hV : 0<V) (hc : (∑i,(c i)^2)≤V) {a : ℝ} (ha : 0≤a) :
    (fairField ι).expect (fun bits => if a≤|fairLinearSum c bits| then 1 else 0)≤
      2*Real.exp (-2*a^2/V) := by
  have oneSide (d : ι → ℝ) (hd : (∑i,(d i)^2)≤V) :
      (fairField ι).expect (fun bits => if a≤fairLinearSum d bits then 1 else 0)≤
        Real.exp (-2*a^2/V) := by
    have H := finite_exp_markov Finset.univ (fairField ι).mass (fairLinearSum d)
      (fun bits _ => (fairField ι).nonneg bits) a (4*a/V) (by positivity)
    have hm : (fairField ι).expect (fun bits => Real.exp ((4*a/V)*fairLinearSum d bits))≤
        Real.exp (V*(4*a/V)^2/8) := by
      apply (fairLinearSum_mgf d (4*a/V)).trans
      apply Real.exp_le_exp.mpr
      gcongr
    have he : (fairField ι).expect (fun bits => if a≤fairLinearSum d bits then 1 else 0)=
        ∑bits∈Finset.univ.filter (fun bits => a≤fairLinearSum d bits),(fairField ι).mass bits := by
      simp only [FiniteLaw.expect,Finset.sum_filter,mul_ite,mul_one,mul_zero]
    rw [he]
    calc
      _ ≤ _ := H
      _ ≤ Real.exp (-(4*a/V)*a)*
          Real.exp (V*(4*a/V)^2/8) := by
        exact mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
      _ = _ := by
        rw [←Real.exp_add]
        congr 1
        field_simp [ne_of_gt hV]
        ring
  have hneg (bits : ι → Bool) : fairLinearSum (fun i => -c i) bits= -fairLinearSum c bits := by
    simp only [fairLinearSum,neg_mul,Finset.sum_neg_distrib]
  have hnegc : (∑i,(-c i)^2)≤V := by simpa only [neg_sq] using hc
  have Hpos := oneSide c hc
  have Hneg := oneSide (fun i => -c i) hnegc
  have hb : (fairField ι).expect (fun bits => if a≤|fairLinearSum c bits| then 1 else 0)≤
      (fairField ι).expect (fun bits => if a≤fairLinearSum c bits then 1 else 0)+
      (fairField ι).expect (fun bits => if a≤fairLinearSum (fun i => -c i) bits then 1 else 0) := by
    have hpoint (bits : ι → Bool) :
        (if a≤|fairLinearSum c bits| then (1:ℝ) else 0)≤
        (if a≤fairLinearSum c bits then 1 else 0)+(if a≤fairLinearSum (fun i => -c i) bits then 1 else 0) := by
      rw [hneg]
      by_cases h : 0≤fairLinearSum c bits
      · rw [abs_of_nonneg h]; split_ifs <;> norm_num
      · rw [abs_of_neg (lt_of_not_ge h)]; split_ifs <;> norm_num
    unfold FiniteLaw.expect
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro bits _
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (hpoint bits) ((fairField ι).nonneg bits)
  linarith

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀i,Fintype (A i)]

theorem expect_dependentProduct_succ {n : ℕ} {A : Fin (n+1) → Type*}
    [∀i,Fintype (A i)] (P : ∀i,FiniteLaw (A i)) (F : (∀i,A i) → ℝ) :
    (dependentProduct P).expect F=(P 0).expect (fun a =>
      (dependentProduct (fun i : Fin n => P i.succ)).expect (fun x => F (Fin.cons a x))) := by
  change (∑x : ∀i,A i,(∏i,(P i).mass (x i))*F x)=_
  rw [←(Fin.consEquiv A).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.consEquiv,Equiv.coe_fn_mk,
    Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,expect,dependentProduct,Finset.mul_sum,mul_assoc]

/-- A genuine dependent Pi-law is invariant under a fixed bijective relabeling
 of slots. No observation is duplicated and no random order is transmitted. -/
theorem dependentProduct_expect_equiv {κ : Type*} [Fintype κ] [DecidableEq κ] (P : ∀i,FiniteLaw (A i))
    (e : κ ≃ ι) (F : (∀i,A i) → ℝ) :
    (dependentProduct P).expect F=(dependentProduct (fun j => P (e j))).expect
      (fun x => F (fun i => cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)))) := by
  let E : (∀j,A (e j)) ≃ (∀i,A i) := Equiv.piCongrLeft A e
  have he (x : ∀j,A (e j)) (i : ι) : E x i=
      cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)) := by
    exact Equiv.piCongrLeft_apply_eq_cast x i
  unfold expect dependentProduct
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  change (∏i,(P i).mass (E x i))*F (E x)=
    (∏j,(P (e j)).mass (x j))*F (fun i => cast (congrArg A (e.apply_symm_apply i)) (x (e.symm i)))
  apply congrArg₂ (· * ·)
  · rw [←e.prod_comp]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    exact Equiv.piCongrLeft_apply_apply A e x j
  · congr 1
    funext i
    exact he x i

end FiniteLaw

/-- Independent heterogeneous emissions in a literal finite chronological
 order accumulate precisely the sum of their trace approximation costs. -/
theorem dependentCoordinate_approximates {n : ℕ} {A : Fin n → Type*}
    [∀i,Fintype (A i)] {q : ℝ} (hq : q∈Set.Icc 0 1)
    (P : ∀i,FiniteLaw (A i)) (f : ∀i,A i → List Bool)
    (w : Fin n → List Bool) (E : Fin n → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.dependentProduct P)
      (fun x => coordinateWord (fun i => f i (x i))) (coordinateWord w) (∑i,E i) := by
  induction n with
  | zero =>
    intro F hF
    change |(FiniteLaw.dependentProduct P).expect (fun _ => F [])-F []|≤∑i : Fin 0,E i
    simp only [FiniteLaw.expect_const,sub_self,abs_zero,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
  | succ n ih =>
    intro F hF
    have ht := ih (fun i => P i.succ) (fun i => f i.succ)
      (fun i => w i.succ) (fun i => E i.succ) (fun i => h i.succ)
    have hh := ApproximatesTrace.append hq (h 0) ht F hF
    rw [FiniteLaw.expect_prod] at hh
    rw [FiniteLaw.expect_dependentProduct_succ,coordinateWord_succ,Fin.sum_univ_succ]
    have he (a : A 0) (x : ∀i : Fin n,A i.succ) :
        coordinateWord (fun i => f i ((Fin.cons a x : ∀i,A i) i))=
          f 0 a++coordinateWord (fun i => f i.succ (x i)) := by
      rw [coordinateWord_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
    simp_rw [he]
    exact hh

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem windowPosterior_mass_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (bits : WindowAssignments T n g Bool b) :
    (windowPosteriorLaw T n g b d).mass bits=
      ∏i : WindowTrial T n g b,(FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i)).mass
          (windowAssignmentEquiv T n g Bool b bits i) := by
  induction b with
  | zero =>
    change (1:ℝ)=∏i : PEmpty,_
    simp
  | succ b ih =>
    change (∏i,(FiniteLaw.flagPosterior (d.1 i)).mass (bits.1 i))*
      ((∏i,(FiniteLaw.flagPosterior (d.2.1 i)).mass (bits.2.1 i))*
        ∏u,(windowPosteriorLaw T n g b (d.2.2 u)).mass (bits.2.2 u))=_
    simp_rw [ih]
    change _=∏i : Fin (n b) ⊕ (Fin (g b) ⊕ (Fin (T b) × WindowTrial T n g b)),
      (FiniteLaw.flagPosterior (match i with
        | .inl k => d.1 k
        | .inr (.inl k) => d.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g (Option Bool) b (d.2.2 u) k)).mass
      (match i with
        | .inl k => bits.1 k
        | .inr (.inl k) => bits.2.1 k
        | .inr (.inr (u,k)) => windowAssignmentEquiv T n g Bool b (bits.2.2 u) k)
    simp only [Fintype.prod_sum_type,Fintype.prod_prod_type]

/-- Exact flat posterior distribution, including all paths and zero-mass
 metadata. This is the same independent bit law, not a new assumption. -/
theorem windowPosterior_expect_flat (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b)
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g b d).expect F=
      (FiniteLaw.indexedProduct (fun i : WindowTrial T n g b => FiniteLaw.flagPosterior
        (windowAssignmentEquiv T n g (Option Bool) b d i))).expect
          (fun bits => F ((windowAssignmentEquiv T n g Bool b).symm bits)) := by
  unfold FiniteLaw.expect FiniteLaw.indexedProduct
  rw [←(windowAssignmentEquiv T n g Bool b).sum_comp]
  apply Finset.sum_congr rfl
  intro bits _
  dsimp only
  rw [Equiv.symm_apply_apply,windowPosterior_mass_flat]

theorem windowPosterior_fair_flat (T n g : ℕ → ℕ) (b : ℕ)
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g b (noReveals T n g b)).expect F=
      (FiniteLaw.indexedProduct (fun _ : WindowTrial T n g b => FiniteLaw.flagPosterior none)).expect
        (fun bits => F ((windowAssignmentEquiv T n g Bool b).symm bits)) := by
  rw [windowPosterior_expect_flat]
  simp only [noReveals,Equiv.apply_symm_apply]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem even_half_cast (t : ℕ) (ht : Even t) : ((t/2:ℕ):ℝ)=(t:ℝ)/2 := by
  have h : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hr : (2:ℝ)*(t/2:ℕ)=t := by exact_mod_cast h
  linarith

theorem scheduledGlobalShift_linear (N t : ℕ) (ht : Even t)
    (bits : Fin ((N/4)*t) → Bool) (u : Fin N) :
    (scheduledGlobalShift N t bits u:ℝ)=
      ∑k,sourceGlobalCoefficient N t u k*((bitIndex (bits k):ℝ)-1/2) := by
  rw [←(globalTrialEquiv N t).sum_comp]
  simp only [Fintype.sum_prod_type,sourceGlobalCoefficient,Equiv.symm_apply_apply]
  unfold scheduledGlobalShift
  simp only [Int.cast_sum,Int.cast_ite,Int.cast_sub,Int.cast_natCast,Int.cast_zero]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hv
  · simp only [one_mul,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    rw [even_half_cast t ht]
    simp only [globalTrialEquiv,Equiv.ofBijective_apply]
    ring
  · simp only [zero_mul,Finset.sum_const_zero]

theorem sourceDisplacement_linear (T n : ℕ → ℕ) (b : ℕ) (ht : Even (n b))
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2)) (u : Fin (T (b+1))) :
    (sourceDisplacement (T (b+1)) (n b) (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)=
      fairLinearSum (sourceGroupCoefficient T n b u)
        (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool (b+2) bits) := by
  rcases bits with ⟨root,global,children⟩
  change Fin ((T (b+1)/4)*n b) → Bool at global
  change Fin (T (b+1)) → ((Fin (n b) → Bool) ×
    (Fin (sourceScheduledTrials T n b) → Bool) ×
    (Fin (T b) → WindowAssignments T n (sourceScheduledTrials T n) Bool b)) at children
  unfold fairLinearSum
  change _=∑i : Fin (n (b+1)) ⊕ (Fin ((T (b+1)/4)*n b) ⊕
      (Fin (T (b+1)) × (Fin (n b) ⊕ (Fin (sourceScheduledTrials T n b) ⊕
        (Fin (T b) × WindowTrial T n (sourceScheduledTrials T n) b))))),_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceGroupCoefficient,
    zero_mul,Finset.sum_const_zero,zero_add,add_zero]
  change _=(∑k,sourceGlobalCoefficient (T (b+1)) (n b) u k*
    ((bitIndex (global k):ℝ)-1/2))+
    (∑v : Fin (T (b+1)),∑a : Fin (n b),
      (if v=u then (1:ℝ) else 0)*((bitIndex ((children v).1 a):ℝ)-1/2))
  have hl : (∑v : Fin (T (b+1)),∑a : Fin (n b),
      (if v=u then (1:ℝ) else 0)*((bitIndex ((children v).1 a):ℝ)-1/2))=
        (∑a : Fin (n b),(bitIndex ((children u).1 a):ℝ))-(n b:ℝ)/2 := by
    simp only [ite_mul,one_mul,zero_mul]
    rw [show (∑v : Fin (T (b+1)),∑a : Fin (n b),
      if v=u then ((bitIndex ((children v).1 a):ℝ)-1/2) else 0)=
        ∑v : Fin (T (b+1)),if v=u then
          (∑a : Fin (n b),((bitIndex ((children v).1 a):ℝ)-1/2)) else 0 from by
            apply Finset.sum_congr rfl
            intro v _
            split_ifs <;> simp]
    rw [Finset.sum_ite_eq',ite_eq_left (Finset.mem_univ u)]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rw [hl,←scheduledGlobalShift_linear (T (b+1)) (n b) ht global u]
  simp only [sourceDisplacement,Int.cast_add,Int.cast_sub,Int.cast_sum,Int.cast_natCast,
    even_half_cast _ ht]
  ring

theorem sourceGroupCoefficient_variance (T n : ℕ → ℕ) (b : ℕ) (u : Fin (T (b+1))) :
    (∑i,(sourceGroupCoefficient T n b u i)^2)≤((T (b+1):ℝ)+1)*(n b:ℝ) := by
  change (∑i : Fin (n (b+1)) ⊕ (Fin ((T (b+1)/4)*n b) ⊕
      (Fin (T (b+1)) × (Fin (n b) ⊕ (Fin (sourceScheduledTrials T n b) ⊕
        (Fin (T b) × WindowTrial T n (sourceScheduledTrials T n) b))))),_)≤_
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,sourceGroupCoefficient,
    zero_pow (by omega : 2≠0),Finset.sum_const_zero,zero_add,add_zero]
  have hg : (∑k : Fin ((T (b+1)/4)*n b),(sourceGlobalCoefficient (T (b+1)) (n b) u k)^2)≤
      ((T (b+1)/4)*n b:ℕ) := by
    calc
      _ ≤ ∑_k : Fin ((T (b+1)/4)*n b),(1:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        dsimp only [sourceGlobalCoefficient]
        split_ifs <;> norm_num
      _ = _ := by simp
  have hl : (∑v : Fin (T (b+1)),∑_a : Fin (n b),(if v=u then (1:ℝ) else 0)^2)=(n b:ℝ) := by
    simp only [ite_pow,one_pow,zero_pow (by omega : 2≠0)]
    simp
  rw [hl]
  have hdiv : ((T (b+1)/4:ℕ):ℝ)≤T (b+1) := by exact_mod_cast Nat.div_le_self (T (b+1)) 4
  push_cast at hg
  have hm := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg (n b): (0:ℝ)≤n b)
  nlinarith only [hg,hm]

/-- Actual per-window unconditional fit tail under the full tree's fair law.
 No independence between different window displacements is asserted. -/
theorem sourceDisplacement_tail (T n : ℕ → ℕ) (b : ℕ) (ht : Even (n b))
    (hn : 0<n b) (u : Fin (T (b+1))) {a : ℝ} (ha : 0≤a) :
    (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+2)
      (noReveals T n (sourceScheduledTrials T n) (b+2))).expect
      (fun bits => if a≤|(sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)| then 1 else 0)≤
      2*Real.exp (-2*a^2/(((T (b+1):ℝ)+1)*(n b:ℝ))) := by
  rw [windowPosterior_fair_flat]
  simp_rw [sourceDisplacement_linear T n b ht,Equiv.apply_symm_apply]
  exact fairLinearSum_tail_variance (sourceGroupCoefficient T n b u)
    (by positivity) (sourceGroupCoefficient_variance T n b u) ha

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem expect_fintype_sum (P : FiniteLaw α) (f : ι → α → ℝ) :
    P.expect (fun a => ∑i,f i a)=∑i,P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_add (P : FiniteLaw α) (f g : α → ℝ) :
    P.expect (fun a => f a+g a)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem coordinateProduct_expect_eval {n : ℕ} (P : Fin n → FiniteLaw α)
    (u : Fin n) (f : α → ℝ) :
    (coordinateProduct P).expect (fun x => f (x u))=(P u).expect f := by
  let F : Fin n → α → ℝ := fun j a => if j=u then f a else 1
  have hp (x : Fin n → α) : (∏j,F j (x j))=f (x u) := by simp [F]
  rw [show (fun x : Fin n → α => f (x u))=(fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm,coordinateProduct_expect_product]
  have hj (j : Fin n) : (P j).expect (F j)=if j=u then (P j).expect f else 1 := by
    by_cases h : j=u <;> simp [F,h,expect_const]
  simp_rw [hj]
  simp

end FiniteLaw

theorem noReveals_succ (T n g : ℕ → ℕ) (b : ℕ) :
    noReveals T n g (b+1)=(fun _ => none,fun _ => none,fun _ => noReveals T n g b) := rfl

theorem windowPosterior_child (T n g : ℕ → ℕ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (u : Fin (T b))
    (F : WindowAssignments T n g Bool b → ℝ) :
    (windowPosteriorLaw T n g (b+1) d).expect (fun bits => F (bits.2.2 u))=
      (windowPosteriorLaw T n g b (d.2.2 u)).expect F := by
  rcases d with ⟨loc,glob,kids⟩
  change ((posteriorArray loc).prod ((posteriorArray glob).prod
    (FiniteLaw.coordinateProduct (fun i => windowPosteriorLaw T n g b (kids i))))).expect
      (fun bits => F (bits.2.2 u))=_
  rw [FiniteLaw.expect_prod]
  simp_rw [FiniteLaw.expect_prod,FiniteLaw.coordinateProduct_expect_eval,FiniteLaw.expect_const]

theorem failure_forall_le_sum {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] [Decidable (∀i,p i)] :
    (if ∀i,p i then (0:ℝ) else 1)≤∑i,if p i then 0 else 1 := by
  by_cases hp : ∀i,p i
  · simp only [ite_eq_left hp]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  · simp only [ite_eq_right hp]
    push Not at hp
    obtain ⟨i,hi⟩ := hp
    calc
      (1:ℝ) = if p i then 0 else 1 := by simp [hi]
      _ ≤ ∑j,if p j then 0 else 1 := by
        apply Finset.single_le_sum (f:=fun j => if p j then (0:ℝ) else 1)
        · intro j _; split_ifs <;> norm_num
        · exact Finset.mem_univ i

end TraceReconstruction

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_Simulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simulation

Canonical and filled simulations, central fit, root words, chronology, slots, finite codes, and complete-trace decoding.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Heterogeneous emissions retain their actual outcome type while moving to
 the one fixed public chronological order. -/
theorem dependentProduct_approximates {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀i,Fintype (A i)] {k : ℕ} {q : ℝ} (hq : q∈Set.Icc 0 1)
    (e : Fin k ≃ ι) (P : ∀i,FiniteLaw (A i)) (f : ∀i,A i → List Bool)
    (w : ι → List Bool) (E : ι → ℝ)
    (h : ∀i,ApproximatesTrace q (P i) (f i) (w i) (E i)) :
    ApproximatesTrace q (FiniteLaw.dependentProduct P)
      (fun x => coordinateWord (fun j => f (e j) (x (e j))))
      (coordinateWord (fun j => w (e j))) (∑i,E i) := by
  intro F hF
  let G := Equiv.piCongrLeft A e
  have he (x : ∀j,A (e j)) (j : Fin k) :
      cast (congrArg A (e.apply_symm_apply (e j))) (x (e.symm (e j)))=x j := by
    rw [←Equiv.piCongrLeft_apply_eq_cast]
    exact Equiv.piCongrLeft_apply_apply A e x j
  rw [FiniteLaw.dependentProduct_expect_equiv P e]
  simp_rw [he]
  have H := dependentCoordinate_approximates hq (fun j => P (e j))
    (fun j => f (e j)) (fun j => w (e j)) (fun j => E (e j)) (fun j => h (e j)) F hF
  rwa [e.sum_comp] at H

namespace PairedMechanisms
variable {Side Leaf : Type} [Fintype Side] [Fintype Leaf] {m k n : ℕ}
variable (M : PairedMechanisms Side m)

theorem slotLaw_mass (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (x : (Fin m → Side × Side) × (Fin k → Side) × (Fin n → Leaf)) :
    (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).mass
      (emissionAssignmentEquiv Side Leaf m k n x)=
    ((FiniteLaw.coordinateProduct (fun j => FiniteLaw.orientedProd (M.first j) (M.second j) (bits j))).prod
      ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).mass x := by
  change (∏i : EmissionSlot m k n,_)=_
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type,Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,slotLaw,emissionAssignmentEquiv,Equiv.coe_fn_mk]
  change (∏j : Fin m,_) * ((∏j : Fin k,_) * ∏j : Fin n,_)=
    (∏j : Fin m,_) * ((∏j : Fin k,_) * ∏j : Fin n,_)
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  cases hb : bits j <;> simp [FiniteLaw.orientedProd,hb,FiniteLaw.prod,mul_comm]

theorem slotLaw_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (F : (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) → ℝ) :
    ((FiniteLaw.coordinateProduct (fun j => FiniteLaw.orientedProd (M.first j) (M.second j) (bits j))).prod
      ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).expect
        (fun x => F (emissionAssignmentEquiv Side Leaf m k n x))=
      (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).expect F := by
  unfold FiniteLaw.expect
  rw [←(emissionAssignmentEquiv Side Leaf m k n).sum_comp]
  simp_rw [slotLaw_mass]

/-- Forgetting only the visible flags recovers the genuine independent side,
 filler and leaf laws at every orientation, before any fit restriction. -/
theorem reportsGiven_slot_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (bits : Fin m → Bool) (θ : Fin n → Bool)
    (F : (∀i : EmissionSlot m k n,EmissionOutcome Side Leaf i) → ℝ) :
    ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ))).expect
      (fun x => F (emissionAssignmentEquiv Side Leaf m k n (fun j => (x.1 j).2,x.2)))=
      (FiniteLaw.dependentProduct (M.slotLaw R P Q bits θ)).expect F := by
  rw [FiniteLaw.expect_prod]
  change (M.reportsGiven bits).expect ((fun z : Fin m → Side × Side =>
    ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ)).expect
      (fun b => F (emissionAssignmentEquiv Side Leaf m k n (z,b)))) ∘
        (fun z j => (z j).2))=_
  rw [←FiniteLaw.expect_map]
  rw [reportsGiven_forget]
  have H := slotLaw_expect M R P Q bits θ F
  rw [FiniteLaw.expect_prod] at H
  exact H

theorem slotCost_sum (E : ℝ) : (∑i : EmissionSlot m k n,slotCost E i)=(n:ℝ)*E := by
  simp only [Fintype.sum_sum_type,slotCost,Finset.sum_const_zero,
    zero_add,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem slotLaw_simulation {q E : ℝ} (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (bits : Fin m → Bool) (θ : Fin n → Bool) (i : EmissionSlot m k n) :
    ApproximatesTrace q (M.slotLaw R P Q bits θ i) (slotDecode f g i)
      (slotWord U V W atom bits θ i) (slotCost E i) := by
  rcases i with ⟨j,b⟩ | i
  · cases b <;> cases hb : bits j <;>
      simp only [slotLaw,slotWord,slotCost,hb,Bool.false_eq_true,ite_false,ite_true]
    · exact (hU j).approximate
    · exact (hV j).approximate
    · exact (hV j).approximate
    · exact (hU j).approximate
  · rcases i with j | j
    · exact (hW j).approximate
    · cases hb : θ j <;> simp only [slotLaw,slotWord,slotCost,hb,Bool.false_eq_true]
      · exact hP
      · exact hQ

/-- Exact conditional-on-orientation simulation boundary. The orientation is
 not part of the common projection, and no fit conditioning enters its law. -/
theorem reportsGiven_simulation {q E : ℝ} (hq : q∈Set.Icc 0 1)
    {L : ℕ} (e : Fin L ≃ EmissionSlot m k n)
    (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (bits : Fin m → Bool) (θ : Fin n → Bool) :
    ApproximatesTrace q
      ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q θ)))
      (fun x => coordinateWord (fun j => slotDecode f g (e j)
        (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))
      (coordinateWord (fun j => slotWord U V W atom bits θ (e j))) ((n:ℝ)*E) := by
  intro F hF
  dsimp only
  rw [M.reportsGiven_slot_expect R P Q bits θ
    (fun z => F (coordinateWord (fun j => slotDecode f g (e j) (z (e j)))))]
  have H := dependentProduct_approximates hq e (M.slotLaw R P Q bits θ) (slotDecode f g)
    (slotWord U V W atom bits θ) (slotCost E)
    (M.slotLaw_simulation R P Q f g U V W atom hU hV hW hP hQ bits θ) F hF
  rwa [slotCost_sum] at H

end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace PairedMechanisms
variable {Side Leaf : Type} [Fintype Side] [Fintype Leaf] {m k n : ℕ}
variable (M : PairedMechanisms Side m)

/-- The actual metadata-first oracle with independent genuine fillers has
 exactly the orientation-first product experiment, in the displayed order. -/
theorem canonical_filled_expect (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (θ : (Fin m → Bool) → Fin n → Bool)
    (F : Reports Side m × (Fin k → Side) × (Fin n → Leaf) → ℝ) :
    ((M.canonicalOracle P Q θ).prod (FiniteLaw.coordinateProduct R)).expect
      (fun x => F (x.1.1,x.2,x.1.2))=
    (fairOrientations m).expect (fun bits =>
      ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod
        (selectedLeafLaw P Q (θ bits)))).expect F) := by
  rw [←M.oracle_factorization,orientationOracle,FiniteLaw.expect_prod,FiniteLaw.expect_mixture]
  simp_rw [FiniteLaw.expect_prod]
  congr 1
  funext bits
  congr 1
  funext z
  exact FiniteLaw.expect_comm _ _ (fun leaf fill => F (z,fill,leaf))

/-- Unconditional common simulation of the actual full canonical oracle.
 The only layout charge is the unconditional fair-orientation failure mass.
 No orientation or side metadata is conditioned on successful fitting. -/
theorem canonical_filled_simulation {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    {L : ℕ} (e : Fin L ≃ EmissionSlot m k n)
    (R : Fin k → FiniteLaw Side) (P Q : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool) (U V : Fin m → List Bool)
    (W : Fin k → List Bool) (atom : Bool → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (U j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (V j))
    (hW : ∀j,SimulatesTrace q (R j) f (W j))
    (hP : ApproximatesTrace q P g (atom false) E) (hQ : ApproximatesTrace q Q g (atom true) E)
    (θ : (Fin m → Bool) → Fin n → Bool) (w : List Bool)
    (good : (Fin m → Bool) → Prop) [DecidablePred good]
    (hword : ∀bits,good bits → coordinateWord
      (fun j => slotWord U V W atom bits (θ bits) (e j))=w) :
    ApproximatesTrace q ((M.canonicalOracle P Q θ).prod (FiniteLaw.coordinateProduct R))
      (fun x => coordinateWord (fun j => slotDecode f g (e j)
        (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1.1 i).2,x.2,x.1.2) (e j))))
      w ((n:ℝ)*E+(fairOrientations m).expect (fun bits => if good bits then 0 else 1)) := by
  intro F hF
  dsimp only
  rw [M.canonical_filled_expect R P Q θ (fun x => F (coordinateWord (fun j => slotDecode f g (e j)
    (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j)))))]
  rw [←FiniteLaw.expect_const (fairOrientations m) (listDeletionExpectation q w F),←FiniteLaw.expect_sub]
  apply (FiniteLaw.abs_expect_le _ _).trans
  calc
    _ ≤ (fairOrientations m).expect (fun bits => (n:ℝ)*E+(if good bits then 0 else 1)) := by
      apply FiniteLaw.expect_mono
      intro bits
      by_cases hb : good bits
      · simp only [ite_eq_left hb,add_zero]
        have H := M.reportsGiven_simulation hq e R P Q f g U V W atom hU hV hW hP hQ bits (θ bits) F hF
        rwa [hword bits hb] at H
      · simp only [ite_eq_right hb]
        have hc := listDeletionExpectation_range hq w F hF
        have hlo := FiniteLaw.expect_mono
          ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q (θ bits))))
          (fun x => (hF (coordinateWord (fun j => slotDecode f g (e j)
            (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))).1)
        have hhi := FiniteLaw.expect_mono
          ((M.reportsGiven bits).prod ((FiniteLaw.coordinateProduct R).prod (selectedLeafLaw P Q (θ bits))))
          (fun x => (hF (coordinateWord (fun j => slotDecode f g (e j)
            (emissionAssignmentEquiv Side Leaf m k n (fun i => (x.1 i).2,x.2) (e j))))).2)
        rw [FiniteLaw.expect_const] at hlo hhi
        have hne : 0≤(n:ℝ)*E := mul_nonneg (Nat.cast_nonneg _) hE
        apply abs_sub_le_iff.mpr
        constructor <;> linarith [hc.1,hc.2]
    _ = _ := by
      unfold FiniteLaw.expect
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,(fairOrientations m).total,one_mul]

end PairedMechanisms
end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The one-based source offset still puts the complete motif in the central
 third under the true fit threshold. The stronger numerical margin is an
 eventual consequence of L=o(T), not an additional stochastic event. -/
theorem source_motif_central (T t s : ℕ) (bits : Fin t → Bool) (v : ℤ)
    (hT : 24 ≤ T) (he : Even T) (hL : 24*2^s ≤ T)
    (hfit : |8*((∑i,(bitIndex (bits i):ℤ))-(t/2:ℕ)+v)| ≤ (T:ℤ))
    (u : Fin T)
    (hu : motifIndicator s ((u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+
      (∑i,(bitIndex (bits i):ℤ))+v)≠0) : u∈centralThird T := by
  have hsupport : 0≤(u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+
      (∑i,(bitIndex (bits i):ℤ))+v ∧
      (u.val:ℤ)-((T/2:ℕ)-1+(t/2:ℕ))+(∑i,(bitIndex (bits i):ℤ))+v < (2^s:ℕ) := by
    by_contra h
    apply hu
    exact ite_eq_right h
  have hh := abs_le.mp hfit
  obtain ⟨k,hk⟩ := he
  have hhalf : 2*(T/2)=T := by omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  omega

/-- Fit controls every internal source motif, retaining all orientations in
 the law. The incoming displacement of the root is supplied separately. -/
theorem sourceTreeFit_central (T n : ℕ → ℕ) (s b : ℕ)
    (center : ℕ → ℤ) (hc : ∀j≤b,center j=sourceLocalCenter T n j)
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (incoming : ℤ)
    (hroot : |8*((∑i,(bitIndex (bits.1 i):ℤ))-(n b/2:ℕ)+incoming)|≤(T b:ℤ))
    (hfit : SourceTreeFit T n (b+1) bits) :
    SourceCentral T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      (fun j => centralThird (T j)) (b+1) bits incoming := by
  induction b generalizing incoming with
  | zero =>
    constructor
    · intro u hu
      rw [hc 0 (by omega)] at hu
      exact source_motif_central (T 0) (n 0) s bits.1 incoming
        (hT 0 (by omega)) (he 0 (by omega)) (hL 0 (by omega)) hroot u hu
    · intro u; trivial
  | succ b ih =>
    constructor
    · intro u hu
      rw [hc (b+1) (by omega)] at hu
      exact source_motif_central (T (b+1)) (n (b+1)) s bits.1 incoming
        (hT (b+1) (by omega)) (he (b+1) (by omega)) (hL (b+1) (by omega)) hroot u hu
    · intro u
      apply ih (fun j hj => hc j (by omega)) (fun j hj => hT j (by omega))
        (fun j hj => he j (by omega)) (fun j hj => hL j (by omega)) _ _ _ (hfit.2 u)
      exact hfit.1 u

/-- The actual root side count has no parity restriction. Its entire range
 lies inside the fit displacement interval when J=o(T). -/
theorem source_root_fit (T J : ℕ) (bits : Fin J → Bool) (h : 4*(J+1)≤T) :
    |8*((∑i,(bitIndex (bits i):ℤ))-(J/2:ℕ))|≤(T:ℤ) := by
  have hlo : (0:ℤ)≤∑i,(bitIndex (bits i):ℤ) := Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hhi : (∑i,(bitIndex (bits i):ℤ))≤J := by
    calc
      _ ≤ ∑_i : Fin J,(1:ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        cases bits i <;> norm_num [bitIndex]
      _ = J := by simp
  apply abs_le.mpr
  omega

theorem sourceNoncentralMass_le_fit (T n : ℕ → ℕ) (s b : ℕ)
    (center : ℕ → ℤ) (hc : ∀j≤b,center j=sourceLocalCenter T n j)
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b)
    (d : WindowAssignments T n (sourceScheduledTrials T n) (Option Bool) (b+1)) :
    sourceNoncentralMass T n (sourceScheduledTrials T n) s center (sourceScheduledShift T n)
      (fun j => centralThird (T j)) (b+1) d 0 ≤
    (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+1) d).expect
      (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1) := by
  apply FiniteLaw.expect_mono
  intro bits
  by_cases hf : SourceTreeFit T n (b+1) bits
  · have hh := sourceTreeFit_central T n s b center hc hT he hL bits 0
      (by simpa only [add_zero] using source_root_fit (T b) (n b) bits.1 hroot) hf
    simp only [ite_eq_left hf,ite_eq_left hh,le_refl]
  · simp only [ite_eq_right hf]
    split_ifs <;> norm_num

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Only interior trials are paired in even bundles. The top J may be odd. -/
theorem sourceTreeWord_eq_center_interior (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ)
    (atom : Bool → List Bool) (b : ℕ) (H : SourceLayoutMargins s P T n h (b-1))
    (htop : ∀j<b,0<T j)
    (hc : ∀j, j+1<b → center j=sourceLocalCenter T n j)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b)
    (incoming : ℤ) (τ : Bool) (hfit : SourceTreeFit T n b bits) :
    sourceTreeWord s P T n h center atom b bits incoming τ=
      sourceCenterWord s P T n center atom b bits incoming τ := by
  induction b using Nat.twoStepInduction generalizing incoming τ with
  | zero => rfl
  | one => rfl
  | more b ih₁ ih₂ =>
    change (Fin (n (b+1)) → Bool) × (Fin ((T (b+1)/4)*n b) → Bool) ×
      (Fin (T (b+1)) → WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) at bits
    let loc : Fin (T (b+1)) → Fin (n b) → Bool := fun u => (bits.2.2 u).1
    let glob := bits.2.1
    let a := P b/2-1
    let A := sourceNominalPre P T b
    let B := sourceNominalPost P T b
    let start := sourceWindowStart (T (b+1)) A (n b) loc glob
    let θ := integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) bits incoming) τ
    have hb : b<b+2-1 := by omega
    have htotal := sourceNominal_total P T b (by have hh := H.ambient b hb; omega)
    have hf (u : Fin (T (b+1))) := sourceWindowStart_oneBased_fit (T (b+1)) (P b) (T b) (n b)
      (2^s) loc glob (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)
    have hx (u : Fin (T (b+1))) :
        sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=((a-start u:ℕ):ℤ) := by
      change sourceNodeAnchor T n center b (bits.2.2 u) (sourceScheduledShift T n (b+1) glob u)=
        ((P b/2-1-sourceWindowStart (T (b+1)) ((P b-T b)/2) (n b) loc glob u:ℕ):ℤ)
      rw [sourceWindowStart_oneBased_anchor (T (b+1)) (P b) (T b) (n b) (2^s) loc glob
        (H.ambient b hb) (H.large b hb) (H.even_window b hb) (H.motif b hb) u (hfit.1 u)]
      simp only [sourceNodeAnchor,hc b (by omega),sourceLocalCenter,sourceScheduledShift,loc]
    have hchild (u : Fin (T (b+1))) :
        sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
          (sourceScheduledShift T n (b+1) glob u) (θ u)=
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) := by
      rw [ih₂ (H.restrict (by omega)) (fun j hj => htop j (by omega)) (fun j hj => hc j (by omega)) _ _ _ (hfit.2 u)]
      simp only [sourceCenterWord,hx,integerTemplateType_nat,complementaryWords]
    have hstartnonneg (u : Fin (T (b+1))) : 0≤(A:ℤ)+sourceDisplacement (T (b+1)) (n b) loc glob u := by
      have he := sourceWindowStart_cast_of_fit (T (b+1)) (P b) (T b) (n b) loc glob
        (H.ambient b hb) (H.large b hb) u (hfit.1 u)
      have hn : (0:ℤ)≤(start u:ℕ) := Int.natCast_nonneg _
      change (start u:ℤ)=(A:ℤ)+_ at he
      omega
    have hp := htop (b+1) (by omega)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T (b+1)≠0)
    have hpart : (List.ofFn (fun u => complementaryWords (P b) a (2^s) (prouhetBool s)
          (sourceBlockWord s P atom b) (θ u))).flatten=
        coordinateWord (fun u => pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
          complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
          pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
      have hh := sourceLayout_literal_partition k A (T b) B (n b) (h b) a (2^s)
      have hk' : k+1=T (b+1) := hk.symm
      rw [hk'] at hh
      rw [show A+T b+B=P b from htotal] at hh
      exact hh (H.even_trials b hb) (H.pre_reserve b hb) (H.post_reserve b hb) loc glob
        (prouhetBool s) (sourceBlockWord s P atom b) θ hstartnonneg
        (fun u => (hf u).2.1) (fun u => (hf u).2.2) (fun u => (hf u).1)
    change coordinateWord (fun u : Fin (T (b+1)) =>
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
      sourceTreeWord s P T n h center atom (b+1) (bits.2.2 u)
        (sourceScheduledShift T n (b+1) glob u) (θ u) ++
      pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u))=
        atomString (T (b+1)) (sourceBlockWord s P atom (b+1)) θ
    calc
      _ = coordinateWord (fun u : Fin (T (b+1)) =>
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++
        complementaryWords (T b) (a-start u) (2^s) (prouhetBool s) (sourceBlockWord s P atom b) (θ u) ++
        pureAtomRun (sourceBlockWord s P atom b false) (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) := by
          apply congrArg coordinateWord
          funext u
          exact congrArg (fun w => pureAtomRun (sourceBlockWord s P atom b false)
            (sourcePreCount (T (b+1)) A (n b) (h b) loc glob u) ++ w ++
              pureAtomRun (sourceBlockWord s P atom b false)
                (sourcePostCount (T (b+1)) B (n b) (h b) loc glob u)) (hchild u)
      _ = _ := hpart.symm



theorem bitIndex_sum_le {J : ℕ} (bits : Fin J → Bool) : (∑i,bitIndex (bits i))≤J := by
  calc
    _ ≤ ∑_i : Fin J,1 := by
      apply Finset.sum_le_sum
      intro i _
      cases bits i <;> norm_num [bitIndex]
    _ = J := by simp

/-- The source root's floor anchor and paired side counts have their literal
 unmarked word interpretation, without requiring J to be even. -/
theorem sourceFullWord_eq_block (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool)
    (b : ℕ) (H : SourceLayoutMargins s P T n h b) (hpos : 0<T b)
    (hroot : P b=n b*(2*h b+1)+T b) (he : Even (T b))
    (hJ : 4*(n b+1)≤T b) (hL : 8*2^s≤T b)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (τ : Bool) (hfit : SourceTreeFit T n (b+1) bits) :
    sourceFullWord s P T n h atom b bits τ=sourceBlockWord s P atom (b+1) τ := by
  let E : ℕ := ∑i,bitIndex (bits.1 i)
  let t := n b*h b+E
  let z := n b*(h b+1)-E
  let a := P b/2-1
  have hE : E≤n b := bitIndex_sum_le bits.1
  have hnat : n b≤n b*(h b+1) := by nlinarith
  have htotal : t+T b+z=P b := by
    have hprod : n b*(h b+1)=n b*h b+n b := by ring
    have hprod2 : n b*(2*h b+1)=2*(n b*h b)+n b := by ring
    dsimp [t,z]
    omega
  obtain ⟨k,hk⟩ := he
  have hhalf : 2*(T b/2)=T b := by omega
  have hP : P b=2*(n b*h b)+n b+T b := by rw [hroot]; ring
  have hPa : P b/2=n b*h b+T b/2+n b/2 := by omega
  have ht : t≤a := by dsimp [t,a]; omega
  have hz : a+2^s≤t+T b := by dsimp [t,a]; omega
  have hanchor : sourceNodeAnchor T n (sourceLocalCenter T n) b bits 0=((a-t:ℕ):ℤ) := by
    have hEc : (E:ℤ)=∑i,(bitIndex (bits.1 i):ℤ) := by simp [E]
    dsimp only [sourceNodeAnchor,sourceLocalCenter]
    have ha : a-t=T b/2-1+n b/2-E := by dsimp [a,t]; omega
    have hTe : 1≤T b/2 := by omega
    have hEe : E≤T b/2-1+n b/2 := by omega
    rw [ha,Nat.cast_sub hEe,Nat.cast_add,Nat.cast_sub hTe,hEc]
    push_cast
    ring
  have ho (j : ℕ) (hj : j<b+1) : 0<T j := by
    by_cases heq : j=b
    · simpa only [heq] using hpos
    · exact H.positive j (by omega)
  have hcenter := sourceTreeWord_eq_center_interior s P T n h (sourceLocalCenter T n) atom
    (b+1) (by simpa using H) ho (fun _ _ => rfl) bits 0 τ hfit
  have hpart := template_word_window t (T b) z a (2^s) (prouhetBool s) τ
    (sourceBlockWord s P atom b) ht hz
  rw [htotal] at hpart
  rw [atomString_constant,atomString_constant] at hpart
  unfold sourceFullWord
  rw [hcenter]
  change pureAtomRun (sourceBlockWord s P atom b false) t ++
    atomString (T b) (sourceBlockWord s P atom b)
      (integerTemplateType (T b) s (sourceNodeAnchor T n (sourceLocalCenter T n) b bits 0) τ) ++
    pureAtomRun (sourceBlockWord s P atom b false) z = _
  rw [hanchor,integerTemplateType_nat]
  exact hpart.symm

end TraceReconstruction



noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem pairedSideCount_false (h : ℕ) (bit : Bool) :
    pairedSideCount h bit false=h+bitIndex bit := by cases bit <;> rfl

theorem pairedSideCount_sum_pre {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) false)=t*h+∑i,bitIndex (bits i) := by
  simp only [pairedSideCount_false,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]

theorem pairedSideCount_sum_total {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) true)+(∑i,bitIndex (bits i))=t*(h+1) := by
  rw [←Finset.sum_add_distrib]
  calc
    _ = ∑_i : Fin t,(h+1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases bits i <;> simp [pairedSideCount,bitIndex]
    _ = _ := by simp

theorem pairedSideCount_sum_post {t h : ℕ} (bits : Fin t → Bool) :
    (∑i,pairedSideCount h (bits i) true)=t*(h+1)-∑i,bitIndex (bits i) := by
  have := pairedSideCount_sum_total (h:=h) bits
  omega

theorem sum_globalSides (N t h : ℕ) (bits : Fin ((N/4)*t) → Bool)
    (side : Bool) (pos : Fin (N/4) → Fin N) (u : Fin N) :
    (∑k : Fin ((N/4)*t), if pos ((globalTrialEquiv N t).symm k).1=u then
      pairedSideCount h (bits k) side else 0)=
    ∑v : Fin (N/4),if pos v=u then
      (∑a : Fin t,pairedSideCount h (bits (globalTrialIndex N t v a)) side) else 0 := by
  rw [←(globalTrialEquiv N t).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Equiv.symm_apply_apply]
  split_ifs with hv
  · rfl
  · simp only [Finset.sum_const_zero]

theorem sourcePreCount_slots (N A t h : ℕ) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    sourcePreCount N A t h loc glob u=
      (∑k : Fin ((N/4)*t),if sourceGlobalPre N t k=u then pairedSideCount h (glob k) false else 0)+
      sourcePreFiller N A t h u+(∑i,pairedSideCount h (loc u i) false) := by
  rw [pairedSideCount_sum_pre]
  change sourcePreFiller N A t h u+(∑v : SourceBundle N,
    if sourceBundleLeft N v=u then sourceBundleCount N t h loc glob v else 0)=_
  rw [Fintype.sum_sum_type]
  have hl : (∑v : Fin N,if sourceBundleLeft N (.inl v)=u then
      sourceBundleCount N t h loc glob (.inl v) else 0)=t*h+∑i,bitIndex (loc u i) := by
    change (∑v : Fin N,if v=u then (t*h+(∑i,bitIndex (loc v i))) else 0)=_
    simp
  rw [hl]
  have hg := sum_globalSides N t h glob false
    (fun v => ⟨v.val,by have := v.isLt; omega⟩) u
  simp only [pairedSideCount_sum_pre] at hg
  change (∑k,if sourceGlobalPre N t k=u then pairedSideCount h (glob k) false else 0)=_ at hg
  rw [hg]
  change _+(_+_) = _+_+_
  have he : (∑v : Fin (N/4),if sourceBundleLeft N (.inr v)=u then
      sourceBundleCount N t h loc glob (.inr v) else 0)=
      ∑v : Fin (N/4),if (⟨v.val,by have := v.isLt; omega⟩ : Fin N)=u then
        (t*h+∑i,bitIndex (glob (globalTrialIndex N t v i))) else 0 := by
    apply Finset.sum_congr rfl
    intro v _
    rfl
  rw [he]
  omega

theorem sourcePostCount_slots (N B t h : ℕ) (ht : Even t) (loc : Fin N → Fin t → Bool)
    (glob : Fin ((N/4)*t) → Bool) (u : Fin N) :
    sourcePostCount N B t h loc glob u=
      (∑i,pairedSideCount h (loc u i) true)+
      (∑k : Fin ((N/4)*t),if sourceGlobalPost N t k=u then pairedSideCount h (glob k) true else 0)+
      sourcePostFiller N B t h u := by
  have hh : 2*(t/2)=t := Nat.mul_div_cancel' ((even_iff_two_dvd).mp ht)
  have hc (bits : Fin t → Bool) :
      2*sourceLayoutReserve t h-(t*h+∑i,bitIndex (bits i))=
        ∑i,pairedSideCount h (bits i) true := by
    rw [pairedSideCount_sum_post]
    dsimp only [sourceLayoutReserve]
    have hs := bitIndex_sum_le bits
    have he : 2*(t*h+t/2)=t*h+t*(h+1) := by
      rw [Nat.mul_add,Nat.mul_add,Nat.mul_one,hh]
      omega
    rw [he]
    omega
  change sourcePostFiller N B t h u+(∑v : SourceBundle N,
    if sourceBundleRight N v=u then 2*sourceLayoutReserve t h-sourceBundleCount N t h loc glob v else 0)=_
  rw [Fintype.sum_sum_type]
  have hl : (∑v : Fin N,if sourceBundleRight N (.inl v)=u then
      2*sourceLayoutReserve t h-sourceBundleCount N t h loc glob (.inl v) else 0)=
      ∑i,pairedSideCount h (loc u i) true := by
    simp only [sourceBundleRight,sourceBundleCount,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hc]
  rw [hl]
  have hg := sum_globalSides N t h glob true
    (fun v => ⟨N-1-v.val,by have := v.isLt; omega⟩) u
  change (∑k,if sourceGlobalPost N t k=u then pairedSideCount h (glob k) true else 0)=_ at hg
  rw [hg]
  simp only [sourceBundleRight,sourceBundleCount,hc]
  omega

/-- Flattening selected equal-atom chunks sums exactly their genuine lengths. -/
theorem filter_chunks_flatten {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List ι) (p : ι → Bool) (c : ι → ℕ) (w : List Bool) :
    ((l.filter p).map (fun i => pureAtomRun w (c i))).flatten=
      pureAtomRun w ((l.map (fun i => if p i then c i else 0)).sum) := by
  calc
    _ = pureAtomRun w (((l.filter p).map c).sum) := by
      simpa only [List.map_map,Function.comp_def] using pureAtomRun_partition w ((l.filter p).map c)
    _ = _ := by
      congr 1
      induction l with
      | nil => rfl
      | cons i l ih => cases hp : p i <;> simp [hp,ih]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceSlotWord_up (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (incoming : ℤ) (τ : Bool) (u : Fin (T b)) (x : TreeEmission T n (sourceScheduledTrials T n) b) :
    sourceSlotWord s P T n h center atom (b+1) bits incoming τ (TreeEmission.up T n (sourceScheduledTrials T n) b u x)=
      sourceSlotWord s P T n h center atom b (bits.2.2 u) (sourceScheduledShift T n b bits.2.1 u)
        (integerTemplateType (T b) s (sourceNodeAnchor T n center b bits incoming) τ u) x := by
  rcases x with ⟨i,p⟩ | f | v <;> rfl

theorem treeChronology_eval (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (f : TreeEmission T n g (b+1) → List Bool) :
    ((treeChronology T n g pre post (b+1)).map f).flatten=
    ((treeLocalSlots T n g b false).map f).flatten ++
      coordinateWord (fun u => ((treeGlobalSlots T n g b false (pre b) u).map f).flatten ++
        f (.inr (.inl (.inl (u,false)))) ++
        ((treeChronology T n g pre post b).map (fun x => f (TreeEmission.up T n g b u x))).flatten ++
        ((treeGlobalSlots T n g b true (post b) u).map f).flatten ++
        f (.inr (.inl (.inl (u,true))))) ++
      ((treeLocalSlots T n g b true).map f).flatten := by
  simp only [treeChronology,List.map_append,List.flatten_append,List.map_flatten,
    List.map_ofFn,coordinateWord]
  congr 2
  rw [List.flatten_flatten,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  simp only [Function.comp_apply,List.map_append,List.flatten_append,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,List.map_map]
  rfl

theorem sourceLocalSlots_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1))
    (incoming : ℤ) (τ side : Bool) :
    ((treeLocalSlots T n (sourceScheduledTrials T n) b side).map
      (sourceSlotWord s P T n h center atom (b+1) bits incoming τ)).flatten=
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (bits.1 i) side) := by
  rcases bits with ⟨loc,glob,kids⟩
  simp only [treeLocalSlots,List.map_ofFn]
  change (List.ofFn (fun i : Fin (n b) => pureAtomRun (sourceBlockWord s P atom b false)
    (pairedSideCount (h b) (loc i) side))).flatten=_
  exact coordinateWord_pureAtomRun _ _

theorem sourceGlobalSlots_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2))
    (incoming : ℤ) (τ side : Bool) (pos : Fin ((T (b+1)/4)*n b) → Fin (T (b+1))) (u : Fin (T (b+1))) :
    ((treeGlobalSlots T n (sourceScheduledTrials T n) (b+1) side pos u).map
      (sourceSlotWord s P T n h center atom (b+2) bits incoming τ)).flatten=
      pureAtomRun (sourceBlockWord s P atom b false)
        (∑k,if pos k=u then pairedSideCount (h b) (bits.2.1 k) side else 0) := by
  rcases bits with ⟨loc,glob,kids⟩
  change Fin ((T (b+1)/4)*n b) → Bool at glob
  simp only [treeGlobalSlots,List.map_map]
  change ((List.filter (fun k => decide (pos k=u)) (List.ofFn id)).map
    (fun i => pureAtomRun (sourceBlockWord s P atom b false) (pairedSideCount (h b) (glob i) side))).flatten=_
  rw [filter_chunks_flatten,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceChronologicalWord_eq_framed (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ)
    (atom : Bool → List Bool) (b : ℕ) (hev : ∀j,j+1<b → Even (n j))
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool b) (incoming : ℤ) (τ : Bool) :
    sourceChronologicalWord s P T n h center atom b bits incoming τ=
      sourceFramedWord s P T n h center atom b bits incoming τ := by
  induction b generalizing incoming τ with
  | zero => simp [sourceChronologicalWord,treeChronology,sourceSlotWord,sourceTreeLeafBool,sourceFramedWord]
  | succ b ih =>
    rcases bits with ⟨loc,glob,kids⟩
    unfold sourceChronologicalWord
    rw [treeChronology_eval]
    erw [sourceLocalSlots_word,sourceLocalSlots_word]
    change _=pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) false) ++
      sourceTreeWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) true)
    apply congrArg (fun w => pureAtomRun (sourceBlockWord s P atom b false)
      (∑i,pairedSideCount (h b) (loc i) false) ++ w ++
      pureAtomRun (sourceBlockWord s P atom b false) (∑i,pairedSideCount (h b) (loc i) true))
    have child (u : Fin (T b)) :
        ((treeChronology T n (sourceScheduledTrials T n) (sourceScheduledPre T n) (sourceScheduledPost T n) b).map
          (fun x => sourceSlotWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ
            (TreeEmission.up T n (sourceScheduledTrials T n) b u x))).flatten=
        sourceFramedWord s P T n h center atom b (kids u) (sourceScheduledShift T n b glob u)
          (integerTemplateType (T b) s (sourceNodeAnchor T n center b (loc,glob,kids) incoming) τ u) := by
      have he : (fun x : TreeEmission T n (sourceScheduledTrials T n) b =>
          sourceSlotWord s P T n h center atom (b+1) (loc,glob,kids) incoming τ
            (TreeEmission.up T n (sourceScheduledTrials T n) b u x)) =
          sourceSlotWord s P T n h center atom b (kids u) (sourceScheduledShift T n b glob u)
            (integerTemplateType (T b) s (sourceNodeAnchor T n center b (loc,glob,kids) incoming) τ u) := by
        funext x
        exact sourceSlotWord_up s P T n h center atom b (loc,glob,kids) incoming τ u x
      erw [he]
      exact ih (fun j hj => hev j (by omega)) (kids u) _ _
    cases b with
    | zero =>
      change coordinateWord _=atomString (T 0) atom _
      apply congrArg coordinateWord
      funext u
      rw [child]
      simp only [treeGlobalSlots,sourceScheduledTrials,List.ofFn_zero,List.filter_nil,List.map_nil,
        List.flatten_nil,List.nil_append,List.append_nil,sourceSlotWord,sourceFillerWord,sourceFramedWord]
    | succ b =>
      change coordinateWord _=coordinateWord _
      apply congrArg coordinateWord
      funext u
      erw [sourceGlobalSlots_word,sourceGlobalSlots_word,child]
      change _=pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePreCount (T (b+1)) (sourceNominalPre P T b) (n b) (h b) (fun v => (kids v).1) glob u) ++
        sourceTreeWord s P T n h center atom (b+1) (kids u) (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) (loc,glob,kids) incoming) τ u) ++
        pureAtomRun (sourceBlockWord s P atom b false)
          (sourcePostCount (T (b+1)) (sourceNominalPost P T b) (n b) (h b) (fun v => (kids v).1) glob u)
      erw [sourcePreCount_slots,sourcePostCount_slots _ _ _ _ (hev b (by omega))]
      change pureAtomRun _ _ ++ pureAtomRun _ _ ++
        (pureAtomRun _ _ ++ sourceTreeWord s P T n h center atom (b+1) (kids u)
          (sourceScheduledShift T n (b+1) glob u)
          (integerTemplateType (T (b+1)) s (sourceNodeAnchor T n center (b+1) (loc,glob,kids) incoming) τ u) ++
          pureAtomRun _ _) ++ pureAtomRun _ _ ++ pureAtomRun _ _ = _
      simp only [sourceScheduledPre,sourceScheduledPost,pureAtomRun_add,List.append_assoc,
        Bool.false_eq_true,ite_false,ite_true]
      rfl

/-- Chronological side/filler/leaf slots produce the SAME full source word
 on the joint fit event. No orientation is removed or conditioned away. -/
theorem sourceChronologicalWord_eq_block (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool)
    (b : ℕ) (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+1)) (τ : Bool)
    (hfit : SourceTreeFit T n (b+1) bits) :
    sourceChronologicalWord s P T n h (sourceLocalCenter T n) atom (b+1) bits 0 τ=
      sourceBlockWord s P atom (b+1) τ := by
  rw [sourceChronologicalWord_eq_framed s P T n h (sourceLocalCenter T n) atom (b+1)
    (fun j hj => H.even_trials j (by omega))]
  have hf := sourceFullWord_eq_block s P T n h atom b H (by omega) hP hT hlarge hmotif bits τ hfit
  change sourceFullWord s P T n h atom b bits τ=_ at hf
  simpa only [sourceFramedWord,sourceFullWord,pairedSideCount_sum_pre,pairedSideCount_sum_post] using hf

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceAssignmentCode_eval (T n : ℕ → ℕ) (A : Type) (b : ℕ)
    (bits : Fin (SourceTrialCount T n b) → A) (j : Fin (SourceTrialCount T n b)) :
    windowAssignmentEquiv T n (sourceScheduledTrials T n) A b
      ((sourceAssignmentCode T n A b).symm bits) (finEnumeration _ j)=bits j := by
  change (sourceAssignmentCode T n A b ((sourceAssignmentCode T n A b).symm bits)) j=bits j
  rw [Equiv.apply_symm_apply]

theorem sourceSlotWord_code (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : Fin (SourceTrialCount T n b) → Bool) (incoming : ℤ) (τ : Bool)
    (x : EmissionSlot (SourceTrialCount T n b) (SourceFillerCount T b) (SourceLeafCount T b)) :
    sourceSlotWord s P T n h center atom b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ
        (sourceEmissionEnum T n b x)=
      PairedMechanisms.slotWord (sourceFlatTrialWord s P T n h atom b false)
        (sourceFlatTrialWord s P T n h atom b true) (sourceFlatFillerWord s P T n h atom b) atom bits
        (sourceFlatLeafType T n s center b incoming τ bits) x := by
  rcases x with ⟨j,p⟩ | f | v
  · cases p <;>
      change sourceTrialWord s P T n h atom b (finEnumeration _ j)
        (Bool.xor (windowAssignmentEquiv T n (sourceScheduledTrials T n) Bool b
          ((sourceAssignmentCode T n Bool b).symm bits) (finEnumeration _ j)) _) = _ <;>
      rw [sourceAssignmentCode_eval] <;> cases he : bits j <;> simp [PairedMechanisms.slotWord,he,sourceFlatTrialWord]
  · rfl
  · rfl

theorem treeChronologyEquiv_word (T n g : ℕ → ℕ)
    (pre post : (b : ℕ) → Fin (g b) → Fin (T b)) (b : ℕ)
    (f : TreeEmission T n g b → List Bool) :
    coordinateWord (fun j => f (treeChronologyEquiv T n g pre post b j))=
      ((treeChronology T n g pre post b).map f).flatten := by
  unfold coordinateWord treeChronologyEquiv
  change (List.ofFn (fun j => f ((treeChronology T n g pre post b).get j))).flatten=_
  have hh : List.map f (List.ofFn (treeChronology T n g pre post b).get) =
      List.ofFn (f ∘ (treeChronology T n g pre post b).get) := List.map_ofFn
  rw [List.ofFn_get] at hh
  exact congrArg List.flatten hh.symm

theorem source_slotCode_word (s : ℕ) (P T n h : ℕ → ℕ) (center : ℕ → ℤ) (atom : Bool → List Bool)
    (b : ℕ) (bits : Fin (SourceTrialCount T n b) → Bool) (incoming : ℤ) (τ : Bool) :
    coordinateWord (fun j => PairedMechanisms.slotWord (sourceFlatTrialWord s P T n h atom b false)
      (sourceFlatTrialWord s P T n h atom b true) (sourceFlatFillerWord s P T n h atom b) atom bits
      (sourceFlatLeafType T n s center b incoming τ bits) (sourceChronologyCode T n b j))=
    sourceChronologicalWord s P T n h center atom b ((sourceAssignmentCode T n Bool b).symm bits) incoming τ := by
  simp_rw [←sourceSlotWord_code]
  simp only [sourceChronologyCode,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact treeChronologyEquiv_word T n (sourceScheduledTrials T n) (sourceScheduledPre T n)
    (sourceScheduledPost T n) b _

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Reindex the genuine independent orientations, retaining the whole source tree. -/
theorem source_fair_code_expect (T n : ℕ → ℕ) (b : ℕ)
    (F : WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℝ) :
    (PairedMechanisms.fairOrientations (SourceTrialCount T n b)).expect
      (fun bits => F ((sourceAssignmentCode T n Bool b).symm bits)) =
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b
      (noReveals T n (sourceScheduledTrials T n) b)).expect F := by
  rw [windowPosterior_fair_flat,FiniteLaw.indexedProduct_expect_equiv _ (finEnumeration _)]
  simp only [PairedMechanisms.fairOrientations,FiniteLaw.expect,FiniteLaw.product,
    FiniteLaw.indexedProduct,sourceAssignmentCode,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr (by ext; simp)
  intro bits _
  rfl

/-- The fit event uses only interior even bundles. In particular no parity
 assumption is made on the top root count J. -/
theorem sourceTreeFit_tail_interior (T n : ℕ → ℕ) (b : ℕ)
    (hn : ∀j,j+1<b → 0<n j) (he : ∀j,j+1<b → Even (n j)) :
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b
      (noReveals T n (sourceScheduledTrials T n) b)).expect
        (fun bits => if SourceTreeFit T n b bits then 0 else 1) ≤ sourceFitTail T n b := by
  induction b using Nat.twoStepInduction with
  | zero =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 0) : SourceTreeFit T n 0 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | one =>
    have hh (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool 1) : SourceTreeFit T n 1 bits := trivial
    simp only [ite_eq_left (hh _),FiniteLaw.expect_const,sourceFitTail,le_refl]
  | more b ih0 ih =>
    let P := windowPosteriorLaw T n (sourceScheduledTrials T n) (b+2)
      (noReveals T n (sourceScheduledTrials T n) (b+2))
    let badShift : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2) → Fin (T (b+1)) → Prop :=
      fun bits u => (T b:ℝ)/8≤|(sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)|
    have hp (bits : WindowAssignments T n (sourceScheduledTrials T n) Bool (b+2)) :
        (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
      let p := fun u : Fin (T (b+1)) => |8*sourceDisplacement (T (b+1)) (n b)
        (fun v => (bits.2.2 v).1) bits.2.1 u|≤(T b:ℤ)
      have hh : (if SourceTreeFit T n (b+2) bits then (0:ℝ) else 1)≤
          (if ∀u,p u then 0 else 1)+(if ∀u,SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1) := by
        by_cases H : SourceTreeFit T n (b+2) bits
        · rw [ite_eq_left H]
          split_ifs <;> norm_num
        · rw [ite_eq_right H]
          by_cases h1 : ∀u,p u
          · have h2 : ¬∀u,SourceTreeFit T n (b+1) (bits.2.2 u) := fun h2 => H ⟨h1,h2⟩
            rw [ite_eq_left h1,ite_eq_right h2]
            norm_num
          · rw [ite_eq_right h1]
            split_ifs <;> norm_num
      apply hh.trans
      apply add_le_add
      · apply (failure_forall_le_sum p).trans
        apply Finset.sum_le_sum
        intro u _
        by_cases hu : p u
        · simp only [ite_eq_left hu]
          split_ifs <;> norm_num
        · have hr : (T b:ℝ)<8*|(sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℝ)| := by
            have hi : (T b:ℤ) < |8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u| := lt_of_not_ge hu
            have hi' : (T b:ℝ) < |(8*sourceDisplacement (T (b+1)) (n b)
              (fun v => (bits.2.2 v).1) bits.2.1 u:ℤ)| := by exact_mod_cast hi
            norm_num only [Int.cast_abs,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<8)] at hi'
            exact hi'
          have hb : badShift bits u := by dsimp [badShift]; linarith
          simp [hu,hb]
      · exact failure_forall_le_sum _
    calc
      _ ≤ P.expect (fun bits => (∑u : Fin (T (b+1)),if badShift bits u then 1 else 0)+
          (∑u : Fin (T (b+1)),if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) :=
            P.expect_mono hp
      _ = (∑u : Fin (T (b+1)),P.expect (fun bits => if badShift bits u then 1 else 0))+
          (∑u : Fin (T (b+1)),P.expect (fun bits => if SourceTreeFit T n (b+1) (bits.2.2 u) then 0 else 1)) := by
            rw [FiniteLaw.expect_add,FiniteLaw.expect_fintype_sum,FiniteLaw.expect_fintype_sum]
      _ ≤ (∑_u : Fin (T (b+1)),2*Real.exp (-2*((T b:ℝ)/8)^2/(((T (b+1):ℝ)+1)*(n b:ℝ))))+
          ∑_u : Fin (T (b+1)),sourceFitTail T n (b+1) := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro u _
              exact sourceDisplacement_tail T n b (he b (by omega)) (hn b (by omega)) u (by positivity)
            · apply Finset.sum_le_sum
              intro u _
              dsimp only [P]
              rw [windowPosterior_child T n (sourceScheduledTrials T n) (b+1)
                (noReveals T n (sourceScheduledTrials T n) (b+2)) u
                (fun x => if SourceTreeFit T n (b+1) x then 0 else 1)]
              rw [noReveals_succ]
              exact ih (fun j hj => hn j (by omega)) (fun j hj => he j (by omega))
      _ = sourceFitTail T n (b+2) := by simp [sourceFitTail,mul_add]


/-- Honest source joint-fit failure after the actual finite coding. -/
theorem source_flat_fit_tail (T n : ℕ → ℕ) (b : ℕ)
    (hn : ∀j,j+1<b → 0<n j) (he : ∀j,j+1<b → Even (n j)) :
    (PairedMechanisms.fairOrientations (SourceTrialCount T n b)).expect
      (fun bits => if SourceTreeFit T n b ((sourceAssignmentCode T n Bool b).symm bits) then 0 else 1)
      ≤ sourceFitTail T n b := by
  rw [source_fair_code_expect T n b (fun bits => if SourceTreeFit T n b bits then 0 else 1)]
  exact sourceTreeFit_tail_interior T n b hn he

/-- The complete canonical oracle now simulates the LITERAL source block.
 All IDs, words, leaf types and chronology instantiate the actual construction.
 The only failed-layout cost is its original unconditional fair-bit mass. -/
theorem source_canonical_simulation {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (hn : ∀j<b,0<n j)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (R : Fin (SourceFillerCount T (b+1)) → FiniteLaw Side) (A B : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (sourceFlatTrialWord s P T n h atom (b+1) false j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (sourceFlatTrialWord s P T n h atom (b+1) true j))
    (hW : ∀j,SimulatesTrace q (R j) f (sourceFlatFillerWord s P T n h atom (b+1) j))
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (τ : Bool) :
    ApproximatesTrace q
      ((M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).prod
        (FiniteLaw.coordinateProduct R))
      (sourceOracleDecode T n (b+1) f g) (sourceBlockWord s P atom (b+1) τ)
      ((SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1)) := by
  let good := fun bits : Fin (SourceTrialCount T n (b+1)) → Bool =>
    SourceTreeFit T n (b+1) ((sourceAssignmentCode T n Bool (b+1)).symm bits)
  have hw (bits : Fin (SourceTrialCount T n (b+1)) → Bool) (hg : good bits) :=
    sourceChronologicalWord_eq_block s P T n h atom b H hP hT hlarge hmotif
      ((sourceAssignmentCode T n Bool (b+1)).symm bits) τ hg
  have hs := M.canonical_filled_simulation hq hE (sourceChronologyCode T n (b+1)) R A B f g
    (sourceFlatTrialWord s P T n h atom (b+1) false)
    (sourceFlatTrialWord s P T n h atom (b+1) true)
    (sourceFlatFillerWord s P T n h atom (b+1)) atom hU hV hW hA hB
    (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)
    (sourceBlockWord s P atom (b+1) τ) good (fun bits hg => by
      rw [source_slotCode_word]
      exact hw bits hg)
  intro F hF
  exact (hs F hF).trans (add_le_add le_rfl (source_flat_fit_tail T n (b+1) (fun j hj => hn j (by omega))
    (fun j hj => H.even_trials j (by omega))))

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ9_TR.TraceReconstruction_SourceOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# SourceOracle

Actual source mechanisms and posteriors, typical metadata, sparse degrees, common-event clipping, approximate oracles, and mixed Hellinger bounds.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Every literal side pair draws its overlap from the correct height of the
source recursion, including reflected global pairs. -/
theorem sourceTrialWord_overlap {q ω : ℝ} (hq : q∈Set.Icc 0 1)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b : ℕ)
    (hov : ∀j<b,ω≤listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
    (i : WindowTrial T n (sourceScheduledTrials T n) b) :
    ω≤listTraceOverlap q hq (sourceTrialWord s P T n h atom b i false)
      (sourceTrialWord s P T n h atom b i true) := by
  induction b with
  | zero => exact PEmpty.elim i
  | succ b ih =>
    rcases i with i | i | ⟨u,i⟩
    · simpa [sourceTrialWord,bitIndex] using hov b (by omega)
    · cases b with
      | zero => exact Fin.elim0 i
      | succ b => simpa [sourceTrialWord,bitIndex] using hov b (by omega)
    · exact ih (fun j hj => hov j (by omega)) i

/-- A common finite side-trace space exists without changing any word. -/
theorem finite_word_bound {ι : Type*} [Fintype ι] (w : ι → List Bool) :
    ∃M,∀i,(w i).length≤M := by
  refine ⟨∑i,(w i).length, fun i => ?_⟩
  exact Finset.single_le_sum (f:=fun i => (w i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Exact change of coordinates for the posterior of all hidden bits, not
 just separate local marginals. -/
theorem source_posterior_code_expect {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b))
    (F : WindowAssignments T n (sourceScheduledTrials T n) Bool b → ℝ) :
    (PairedMechanisms.orientationsGiven z).expect
      (fun bits => F ((sourceAssignmentCode T n Bool b).symm bits)) =
    (windowPosteriorLaw T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z)).expect F := by
  rw [windowPosterior_expect_flat,FiniteLaw.indexedProduct_expect_equiv _ (finEnumeration _)]
  simp only [sourceReportFlags,sourceAssignmentCode_eval]
  simp only [PairedMechanisms.orientationsGiven,FiniteLaw.expect,FiniteLaw.coordinateProduct,
    FiniteLaw.indexedProduct,sourceAssignmentCode,Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr (by ext; simp)
  intro bits _
  rfl

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace PairedMechanisms
variable {Side : Type*} [Fintype Side] {m : ℕ} (M : PairedMechanisms Side m)

theorem hiddenSubset_mgf (S : Finset (Fin m)) {ω t : ℝ} (hw : ∀i,M.hiddenWeight i=ω)
    (hp : ω^2∈Set.Icc 0 1) (ht : |t|≤1) :
    M.reports.expect (fun z => Real.exp (t*((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)))≤
      Real.exp ((S.card:ℝ)*t^2) := by
  have he (z : Reports Side m) :
      Real.exp (t*((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2))=
        ∏i : S,Real.exp (t*((hiddenTrial (z i.val).1:ℕ)-ω^2)) := by
    rw [←Real.exp_sum]
    congr 1
    simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
      nsmul_eq_mul,hiddenSubset,Nat.cast_sum]
    ring
  simp_rw [he]
  rw [reports,FiniteLaw.coordinateProduct_expect_subtype _ S
    (fun (_ : S) (z : Option Bool × (Side × Side)) => Real.exp (t*((hiddenTrial z.1:ℕ)-ω^2)))]
  calc
    _ ≤ ∏i : S,Real.exp (t^2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.sum_nonneg (fun z _ => mul_nonneg
          ((FiniteLaw.pairedReport (M.first i.val) (M.second i.val) (M.common i.val) (M.weight_nonneg i.val)
            (M.common_first i.val) (M.common_second i.val)).nonneg z) (Real.exp_nonneg _))
      · intro i _
        have h := FiniteLaw.pairedReport_hidden_mgf (M.first i.val) (M.second i.val) (M.common i.val)
          (M.weight_nonneg i.val) (M.common_first i.val) (M.common_second i.val) (by simpa [hw i.val] using hp) ht
        simpa only [hw i.val] using h
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe,Real.exp_nat_mul]

/-- A quantitative unconditional bound for failure of a source hidden-count
 condition. The exponent ω⁴m is sufficient for the uniform scale margins. -/
theorem hiddenSubset_small (S : Finset (Fin m)) {ω : ℝ} (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2 then 1 else 0)≤
      Real.exp (-(S.card:ℝ)*ω^4/16) := by
  have ht : 0≤ω^2/4 := by positivity
  have ht' : |-(ω^2/4)|≤1 := by rw [abs_neg,abs_of_nonneg ht]; linarith [hp.2]
  have H := finite_exp_markov Finset.univ M.reports.mass
    (fun z => -((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)) (fun z _ => M.reports.nonneg z)
    ((S.card:ℝ)*ω^2/2) (ω^2/4) ht
  have hm := M.hiddenSubset_mgf S hw hp ht'
  have hsub : M.reports.expect (fun z => if (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2 then 1 else 0)≤
      ∑z∈Finset.univ.filter (fun z => (S.card:ℝ)*ω^2/2≤-((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)),M.reports.mass z := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    dsimp only
    by_cases hz : (hiddenSubset S z:ℝ)<(S.card:ℝ)*ω^2/2
    · rw [ite_eq_left hz,ite_eq_left (by linarith : (S.card:ℝ)*ω^2/2≤-((hiddenSubset S z:ℕ)-(S.card:ℝ)*ω^2)),mul_one]
    · rw [ite_eq_right hz,mul_zero]; split_ifs <;> positivity [M.reports.nonneg z]
  calc
    _ ≤ _ := hsub.trans H
    _ ≤ Real.exp (-(ω^2/4)*((S.card:ℝ)*ω^2/2))*Real.exp ((S.card:ℝ)*(-(ω^2/4))^2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa only [FiniteLaw.expect,neg_mul,mul_neg,neg_neg] using hm
    _ = _ := by rw [←Real.exp_add]; congr 1; ring


end PairedMechanisms
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem collectionTrial_injective (T n g : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Function.Injective (collectionTrial T n g b v) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with v | ⟨u,v⟩
    · cases v
      · intro i j h
        exact Sum.inl.inj h
      · intro i j h
        exact Sum.inl.inj (Sum.inr.inj h)
    · intro i j h
      apply ih v
      exact congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj h))

theorem collectionFlags_trial (T n g : ℕ → ℕ) {A : Type} (b : ℕ)
    (d : WindowAssignments T n g A b) (v : WindowCollection T b)
    (j : Fin (collectionCount T n g b v)) :
    collectionFlags T n g b d v j=
      windowAssignmentEquiv T n g A b d (collectionTrial T n g b v j) := by
  induction b with
  | zero => exact PEmpty.elim v
  | succ b ih =>
    rcases v with v | ⟨u,v⟩
    · cases v <;> rfl
    · exact ih (d.2.2 u) v j

theorem hiddenCollectionConditions_iff (T n g : ℕ → ℕ) (ω : ℝ) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) :
    HiddenCollectionConditions T n g ω b d ↔
      ∀v : WindowCollection T b,(collectionCount T n g b v:ℝ)*ω^2/2≤
        ∑i,(hiddenTrial (collectionFlags T n g b d v i):ℝ) := by
  induction b with
  | zero => simp [HiddenCollectionConditions,WindowCollection]
  | succ b ih =>
    constructor
    · intro h v
      rcases v with v | ⟨u,v⟩
      · cases v
        · exact h.1
        · exact h.2.1
      · exact (ih (d.2.2 u)).mp (h.2.2 u) v
    · intro h
      refine ⟨h (.inl false),h (.inl true),fun u => (ih (d.2.2 u)).mpr ?_⟩
      intro v
      exact h (.inr (u,v))

theorem sourceCollectionIndex_injective (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    Function.Injective (sourceCollectionIndex T n b v) :=
  (finEnumeration _).symm.injective.comp (collectionTrial_injective T n _ b v)

theorem sourceCollectionSet_card (T n : ℕ → ℕ) (b : ℕ) (v : WindowCollection T b) :
    (sourceCollectionSet T n b v).card=collectionCount T n (sourceScheduledTrials T n) b v := by
  rw [sourceCollectionSet,Finset.card_image_of_injective _ (sourceCollectionIndex_injective T n b v)]
  simp only [Finset.card_univ,Fintype.card_fin]

theorem sourceCollection_flags {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) (v : WindowCollection T b)
    (j : Fin (collectionCount T n (sourceScheduledTrials T n) b v)) :
    collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v j=
      (z (sourceCollectionIndex T n b v j)).1 := by
  rw [collectionFlags_trial]
  have h := sourceAssignmentCode_eval T n (Option Bool) b (fun j => (z j).1)
    (sourceCollectionIndex T n b v j)
  simpa only [sourceCollectionIndex,Equiv.apply_symm_apply,sourceReportFlags] using h

theorem sourceCollection_hidden {Side : Type*} (T n : ℕ → ℕ) (b : ℕ)
    (z : Reports Side (SourceTrialCount T n b)) (v : WindowCollection T b) :
    PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z=
      ∑i,hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i) := by
  unfold PairedMechanisms.hiddenSubset
  rw [←Finset.sum_subtype (sourceCollectionSet T n b v) (fun _ => Iff.rfl)
    (fun j => hiddenTrial (z j).1)]
  rw [sourceCollectionSet,Finset.sum_image]
  · simp_rw [sourceCollection_flags]
  · exact (sourceCollectionIndex_injective T n b v).injOn

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The actual noncentral posterior mass has the unconditional honest
 fit-error bound. Impossible reports cause no problem in Bayes averaging. -/
theorem source_noncentral_average {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) :
    M.reports.expect (fun z => sourceNoncentralMass T n (sourceScheduledTrials T n) s
      (sourceLocalCenter T n) (sourceScheduledShift T n) (fun j => centralThird (T j))
      (b+1) (sourceReportFlags T n (b+1) z) 0) ≤ sourceFitTail T n (b+1) := by
  calc
    _ ≤ M.reports.expect (fun z =>
        (windowPosteriorLaw T n (sourceScheduledTrials T n) (b+1) (sourceReportFlags T n (b+1) z)).expect
          (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1)) := by
      apply FiniteLaw.expect_mono
      intro z
      exact sourceNoncentralMass_le_fit T n s b (sourceLocalCenter T n) (fun _ _ => rfl)
        hT he hL hroot _
    _ = M.reports.expect (fun z => (PairedMechanisms.orientationsGiven z).expect
        (fun bits => if SourceTreeFit T n (b+1) ((sourceAssignmentCode T n Bool (b+1)).symm bits) then 0 else 1)) := by
      apply congrArg (FiniteLaw.expect M.reports)
      funext z
      exact (source_posterior_code_expect T n (b+1) z
        (fun bits => if SourceTreeFit T n (b+1) bits then 0 else 1)).symm
    _ = _ := M.posterior_average _
    _ ≤ _ := source_flat_fit_tail T n (b+1) (fun j hj => hn j (by omega)) (fun j hj => hne j (by omega))

/-- Markov for a genuine finite law, stated for the exact failure indicator. -/
theorem FiniteLaw.positive_markov {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (hf : ∀x,0≤f x) {a : ℝ} (ha : 0<a) :
    P.expect (fun x => if a≤f x then 1 else 0) ≤ P.expect f/a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm,←FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono
  intro x
  split_ifs with hx
  · simpa only [mul_one] using hx
  · simpa only [mul_zero] using hf x

end TraceReconstruction


noncomputable section


noncomputable section

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem density_score_centered (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀a,Q.mass a=P.mass a*(1+Z a)) : P.expect Z=0 := by
  have h := Q.total
  simp_rw [hZ,mul_add,mul_one,Finset.sum_add_distrib,P.total] at h
  change _+P.expect Z=1 at h
  linarith

end TraceReconstruction.FiniteLaw

noncomputable section
namespace TraceReconstruction.FiniteLaw
open scoped Classical
variable {α : Type*} [Fintype α]

theorem eventMass_indicator (P : FiniteLaw α) (A : Finset α) :
    P.eventMass A=P.expect (fun a => if a∈A then 1 else 0) := by
  simp only [expect,mul_ite,mul_one,mul_zero,←Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter,eventMass]

end TraceReconstruction.FiniteLaw

noncomputable section

noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem source_hidden_conditions_effective_tail {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n b))
    (ω : ℝ) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1) :
    M.reports.expect (fun z => if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω b
      (sourceReportFlags T n b z) then 0 else 1) ≤ sourceEffectiveHiddenTail T n b ω := by
  calc
    _ ≤ M.reports.expect (fun z => ∑v : WindowCollection T b,
      if (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
        ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
      then 0 else 1) := by
        apply FiniteLaw.expect_mono
        intro z
        simp only [hiddenCollectionConditions_iff]
        exact failure_forall_le_sum _
    _ = ∑v : WindowCollection T b,M.reports.expect (fun z =>
      if (PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
        ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 then 1 else 0) := by
        rw [FiniteLaw.expect_fintype_sum]
        apply Finset.sum_congr rfl
        intro v _
        apply congrArg (FiniteLaw.expect M.reports)
        funext z
        rw [sourceCollectionSet_card,sourceCollection_hidden,Nat.cast_sum]
        by_cases h : (collectionCount T n (sourceScheduledTrials T n) b v:ℝ)*ω^2/2≤
          ∑i,(hiddenTrial (collectionFlags T n (sourceScheduledTrials T n) b (sourceReportFlags T n b z) v i):ℝ)
        · simp [h,not_lt.mpr h]
        · simp [h,lt_of_not_ge h]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hc : collectionCount T n (sourceScheduledTrials T n) b v=0
      · rw [ite_eq_left hc]
        have hz : M.reports.expect (fun z =>
            if (PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
              ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 then 1 else 0)=0 := by
          have h (z : Reports Side (SourceTrialCount T n b)) :
              ¬(PairedMechanisms.hiddenSubset (sourceCollectionSet T n b v) z:ℝ)<
                ((sourceCollectionSet T n b v).card:ℝ)*ω^2/2 := by
            rw [sourceCollectionSet_card,hc]
            simp only [Nat.cast_zero,zero_mul,zero_div]
            exact not_lt.mpr (Nat.cast_nonneg _)
          simp_rw [ite_eq_right (h _)]
          exact FiniteLaw.expect_const _ 0
        exact hz.le
      · rw [ite_eq_right hc]
        simpa only [sourceCollectionSet_card] using M.hiddenSubset_small (sourceCollectionSet T n b v) hw hp

theorem source_typical_effective_failure {Side : Type*} [Fintype Side]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (ω a : ℝ) (ha : 0<a) (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1)
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hL : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) :
    M.reports.expect (fun z => if SourceTypical T n s b ω a z then 0 else 1) ≤
      sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a := by
  let f := fun z : Reports Side (SourceTrialCount T n (b+1)) =>
    sourceNoncentralMass T n (sourceScheduledTrials T n) s (sourceLocalCenter T n)
      (sourceScheduledShift T n) (fun j => centralThird (T j)) (b+1)
      (sourceReportFlags T n (b+1) z) 0
  calc
    _ ≤ M.reports.expect (fun z =>
        (if HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z) then 0 else 1)+(if a≤f z then 1 else 0)) := by
      apply FiniteLaw.expect_mono
      intro z
      by_cases H : SourceTypical T n s b ω a z
      · rw [ite_eq_left H]
        split_ifs <;> norm_num
      · rw [ite_eq_right H]
        by_cases h : HiddenCollectionConditions T n (sourceScheduledTrials T n) ω (b+1)
          (sourceReportFlags T n (b+1) z)
        · have hf : ¬f z<a := fun hf => H ⟨h,hf⟩
          rw [ite_eq_left h,ite_eq_left (le_of_not_gt hf)]
          norm_num
        · rw [ite_eq_right h]
          split_ifs <;> norm_num
    _ ≤ _ := by
      rw [FiniteLaw.expect_add]
      apply add_le_add (source_hidden_conditions_effective_tail T n (b+1) M ω hw hp)
      apply (M.reports.positive_markov f (fun z => sourceNoncentralMass_nonneg T n _ s _ _ _ _ _ _) ha).trans
      exact div_le_div_of_nonneg_right
        (source_noncentral_average T n s b M hn hne hT he hL hroot) ha.le


end TraceReconstruction

noncomputable section

noncomputable section



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceOracle_withDensity {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P Q : FiniteLaw Leaf) (Z : Leaf → ℝ) (hden : ∀a,Q.mass a=P.mass a*(1+Z a))
    (hZ : ∀a,0 ≤ 1+Z a) (hc : P.expect Z=0) (τ : Bool) :
    M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)=
      (sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
        (sourceOracleDensity_nonneg T n s b Z hZ τ)
        (sourceOracleDensity_total T n s b M P Z hc τ) := by
  apply FiniteLaw.ext
  funext zx
  exact M.canonicalOracle_density P Q Z hden _ zx.1 zx.2

attribute [local instance] OAI.TraceReconstruction.instDecidableEqProd_solutions
theorem sourceTypicalSet_mass {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (s b : ℕ) (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (P Q : FiniteLaw Leaf) (ω a : ℝ) (τ : Bool) :
    (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).eventMass
      (sourceTypicalSet T n s b ω a)ᶜ=
      M.reports.expect (fun z => if SourceTypical T n s b ω a z then 0 else 1) := by
  rw [FiniteLaw.eventMass_indicator]
  calc
    _ = (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)).expect
        (fun zx => if SourceTypical T n s b ω a zx.1 then 0 else 1) := by
      apply congrArg (FiniteLaw.expect _)
      funext zx
      simp [sourceTypicalSet]
    _ = _ := M.canonicalOracle_metadata P Q
      (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 τ)
      (fun z => if SourceTypical T n s b ω a z then 0 else 1)

/-- Complete finite quantitative clipping of the actual recursive source
 oracle. All analytic budgets here are explicit arithmetic in the literal
 branching/trial counts; no coefficient or oracle-existence premise remains. -/
theorem source_clippedOracle_exists {Side Leaf : Type*} [Fintype Side] [Fintype Leaf]
    (T n : ℕ → ℕ) (hTpos : ∀j,0<T j) (s b R k : ℕ)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1))) (P Q : FiniteLaw Leaf)
    (Z : Leaf → ℝ) (hden : ∀a,Q.mass a=P.mass a*(1+Z a)) (hZ : ∀a,0 ≤ 1+Z a)
    (ω a η L : ℝ) (ha : 0<a) (hL : 0<L)
    (hw : ∀i,M.hiddenWeight i=ω) (hp : ω^2∈Set.Icc 0 1)
    (hn : ∀j,j<b → 0<n j) (hne : ∀j,j<b → Even (n j))
    (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j)) (hMotif : ∀j≤b,24*2^s≤T j)
    (hroot : 4*(n b+1)≤T b) (hk : 1 ≤ k)
    (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2) :
    Nonempty (ClippedOracle
      (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false))
      (M.canonicalOracle P Q (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true))
      k (sourceClippingCost T n s b k ω a L)
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  have hc := FiniteLaw.density_score_centered P Q Z hden
  have hB (τ : Bool) : ((sourceReferenceLaw T n b M P).withDensity (sourceOracleDensity T n s b Z τ)
      (sourceOracleDensity_nonneg T n s b Z hZ τ) (sourceOracleDensity_total T n s b M P Z hc τ)).eventMass
        (sourceTypicalSet T n s b ω a)ᶜ ≤ sourceEffectiveHiddenTail T n (b+1) ω+sourceFitTail T n (b+1)/a := by
    rw [←sourceOracle_withDensity T n s b M P Q Z hden hZ hc τ,sourceTypicalSet_mass]
    exact source_typical_effective_failure T n s b M ω a ha hw hp hn hne hT he hMotif hroot
  rw [sourceOracle_withDensity T n s b M P Q Z hden hZ hc false,
    sourceOracle_withDensity T n s b M P Q Z hden hZ hc true]
  exact source_reference_clipped_exists T n hTpos s b R k M P Z hZ hc ω a η L ha.le hL hk hMoment hscale hη hB herror

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem ApproximatesTrace.of_tv {α : Type*} [Fintype α]
    {q E e : ℝ} {P Q : FiniteLaw α} {f : α → List Bool} {w : List Bool}
    (hP : ApproximatesTrace q P f w E) (htv : Q.tv P ≤ e) :
    ApproximatesTrace q Q f w (e+E) := by
  intro F hF
  exact (abs_sub_le (Q.expect (fun a => F (f a))) (P.expect (fun a => F (f a)))
    (listDeletionExpectation q w F)).trans (add_le_add
      ((FiniteLaw.abs_expect_sub_le_tv Q P _ (fun a => hF _)).trans htv) (hP F hF))

/-- The clipping and independent filler metadata preserve the source's fixed
 public trace decoder. -/
theorem source_clipped_simulation {Side Leaf : Type} [Fintype Side] [Fintype Leaf]
    {q E e V : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b k : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hP : P b=n b*(2*h b+1)+T b) (hT : Even (T b))
    (hlarge : 4*(n b+1)≤T b) (hmotif : 8*2^s≤T b)
    (hn : ∀j<b,0<n j)
    (M : PairedMechanisms Side (SourceTrialCount T n (b+1)))
    (R : Fin (SourceFillerCount T (b+1)) → FiniteLaw Side) (A B : FiniteLaw Leaf)
    (f : Side → List Bool) (g : Leaf → List Bool)
    (hU : ∀j,SimulatesTrace q (M.first j) f (sourceFlatTrialWord s P T n h atom (b+1) false j))
    (hV : ∀j,SimulatesTrace q (M.second j) f (sourceFlatTrialWord s P T n h atom (b+1) true j))
    (hW : ∀j,SimulatesTrace q (R j) f (sourceFlatFillerWord s P T n h atom (b+1) j))
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (C : ClippedOracle
      (M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 false))
      (M.canonicalOracle A B (sourceFlatLeafType T n s (sourceLocalCenter T n) (b+1) 0 true)) k e V) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (e+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1)) V) := by
  let D := C.prod (FiniteLaw.coordinateProduct R)
  refine ⟨{
    Outcome := (Reports Side (SourceTrialCount T n (b+1)) × (Fin (SourceLeafCount T (b+1)) → Leaf)) ×
      (Fin (SourceFillerCount T (b+1)) → Side)
    finiteOutcome := inferInstance
    first := D.first
    second := D.second
    decode := sourceOracleDecode T n (b+1) f g
    score := D.score
    density := D.density
    likelihood_nonneg := D.likelihood_nonneg
    centered := D.centered
    moment := D.moment
    first_simulation := ?_
    second_simulation := ?_
  }⟩
  · simpa only [add_assoc] using
      (source_canonical_simulation hq hE s P T n h atom b H hP hT hlarge hmotif hn M R A B f g hU hV hW hA hB false).of_tv D.first_tv
  · simpa only [add_assoc] using
      (source_canonical_simulation hq hE s P T n h atom b H hP hT hlarge hmotif hn M R A B f g hU hV hW hA hB true).of_tv D.second_tv

end TraceReconstruction


noncomputable section


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Literal recursive source oracle with actual complete-trace side laws.
 All remaining hypotheses here are explicit parameter inequalities, the old
 leaf oracle, and its genuine repeated-word overlap invariant. -/
theorem actual_source_oracle_oai {Leaf : Type} [Fintype Leaf]
    {q E : ℝ} (hq : q∈Set.Icc 0 1) (hE : 0≤E)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b R k : ℕ)
    (H : SourceLayoutMargins s P T n h b)
    (hTpos : ∀j,0<T j) (hP : P b=n b*(2*h b+1)+T b)
    (hn : ∀j<b,0<n j) (hT : ∀j≤b,24≤T j) (he : ∀j≤b,Even (T j))
    (hMotif : ∀j≤b,24*2^s≤T j) (hroot : 4*(n b+1)≤T b)
    (A B : FiniteLaw Leaf) (g : Leaf → List Bool) (Z : Leaf → ℝ)
    (hden : ∀a,B.mass a=A.mass a*(1+Z a)) (hZ : ∀a,0≤1+Z a)
    (hA : ApproximatesTrace q A g (atom false) E) (hB : ApproximatesTrace q B g (atom true) E)
    (ω a η L : ℝ) (ha : 0<a) (hL : 0<L) (hω : ω∈Set.Ioo 0 1)
    (hov : ∀j<b+1,ω≤listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)))
    (hk : 1≤k) (hMoment : A.expect (fun a => |Z a|^(2*k))≤L^(2*k))
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b≤1/2)
    (hη : ∀j<b+1,hiddenSmoothingBound (n j) s ω≤η)
    (herror : sourceClippingCost T n s b k ω a L≤1/2) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (sourceClippingCost T n s b k ω a L+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1))
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  let U := sourceFlatTrialWord s P T n h atom (b+1) false
  let V := sourceFlatTrialWord s P T n h atom (b+1) true
  let W := sourceFlatFillerWord s P T n h atom (b+1)
  obtain ⟨mU,hmU⟩ := finite_word_bound U
  obtain ⟨mV,hmV⟩ := finite_word_bound V
  obtain ⟨mW,hmW⟩ := finite_word_bound W
  let m := max mU (max mV mW)
  have hU (j) : (U j).length ≤ m := (hmU j).trans (le_max_left _ _)
  have hV (j) : (V j).length ≤ m := (hmV j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hW (j) : (W j).length ≤ m := (hmW j).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hov' (j) : ω≤listTraceOverlap q hq (U j) (V j) :=
    sourceTrialWord_overlap hq s P T n h atom (b+1) hov (finEnumeration _ j)
  let M := tracePairedMechanisms hq hω.1 U V m hU hV hov'
  let F : Fin (SourceFillerCount T (b+1)) → FiniteLaw (BoundedTrace m) :=
    fun j => listTraceLaw q hq (W j) m (hW j)
  have hp : ω^2∈Set.Icc 0 1 := ⟨sq_nonneg ω,by nlinarith [hω.1,hω.2]⟩
  obtain ⟨C⟩ := source_clippedOracle_exists T n hTpos s b R k M A B Z hden hZ ω a η L ha hL
    (fun _ => rfl) hp hn H.even_trials hT he hMotif hroot hk hMoment hscale hη herror
  apply source_clipped_simulation hq hE s P T n h atom b k H hP (he b le_rfl) hroot
    (by nlinarith [hMotif b le_rfl]) hn M F A B Subtype.val g
    (fun j => listTraceLaw_simulates q hq (U j) m (hU j))
    (fun j => listTraceLaw_simulates q hq (V j) m (hV j))
    (fun j => listTraceLaw_simulates q hq (W j) m (hW j)) hA hB C

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.TraceReconstruction.actual_source_oracle_oai := @OAI.TraceReconstruction.actual_source_oracle_oai
