-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_entropy_pair_with_budget
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:11:36.46253+00:00
-- url     : https://prove2.me/submissions/3c47ddf5-a563-4691-97fe-9cfa0ce2308e

import Mathlib
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights
import Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression
import Theorems.Thm_OAI_MetricEntropyDuality_exists_robust_directions_of_budget
import Theorems.Thm_OAI_MetricEntropyDuality_exists_prime_for_rank
import Theorems.Thm_OAI_MetricEntropyDuality_FieldGraphSeparation_no_short_walk
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_phi_eq_zero_of_le
import Theorems.Thm_OAI_MetricEntropyDuality_log_count_le_encodingCost
import Theorems.Thm_OAI_MetricEntropyDuality_entropyPair_of_matrix
import Theorems.Thm_OAI_MetricEntropyDuality_uniform_compression

open OAI OAI.MetricEntropyDuality
lemma h51e_card_form (p r k : ℕ) [Fact p.Prime] :
    Fintype.card (SymmetricForm (ZMod p) r k) = p ^ formDimension r k := by
  unfold SymmetricForm formDimension
  rw [Fintype.card_fun, ZMod.card, Sym.card_sym_eq_choose, Fintype.card_fin]

theorem solution (a : ℝ) (ha : 1 ≤ a)
    (r : ℕ) (hr : 1 ≤ r) (B : ℝ) (hB : 0 < B) :
    Nonempty (EntropyPair a r B) := by
  classical
  have hr0 : 0 < r := by omega
  obtain ⟨p, hp, -, hph, hpsize, hpexp, -, -, -, -⟩ := exists_prime_for_rank ha hr0 B 0 hB
  haveI : Fact p.Prime := ⟨hp⟩
  have hθ0 : 0 < accuracy a := by unfold accuracy; positivity
  have hθ1 : accuracy a < 1 := by
    unfold accuracy; rw [div_lt_one (by positivity)]; linarith
  set j := Nat.ceil (Real.exp (Real.log 3 / accuracy a)) with hjdef
  have hhj : compressionRadius a = j + 1 := rfl
  set θ := accuracy a with hθdef
  set u := directionCount r (j + 1) θ with hudef
  set s := pivotSlots θ with hsdef
  set D := formDimension r (j + 1) with hDdef
  have hD1 : 1 ≤ D := by
    rw [hDdef]; unfold formDimension; exact Nat.choose_pos (by omega)
  have hu : 0 < u := by
    rw [hudef]; unfold directionCount
    apply Nat.ceil_pos.mpr
    have : (1:ℝ) ≤ D := by exact_mod_cast hD1
    positivity
  have hdel : ((j + 1 : ℕ) : ℝ) * (2 * (D : ℝ)) ≤ θ * (u : ℝ) := by
    have := Nat.le_ceil (((j + 1 : ℕ) : ℝ) * (2 * (D : ℝ)) / θ)
    rw [div_le_iff₀ hθ0] at this
    have e : u = Nat.ceil (((j + 1 : ℕ) : ℝ) * (2 * (D : ℝ)) / θ) := rfl
    rw [e]; linarith
  obtain ⟨t, ht⟩ := exists_robust_directions_of_budget (p := p) (r := r) (h := j + 1) (u := u)
    hr0 (Nat.succ_pos j) hu hθ1 hdel hph hpsize
  -- the vertex set, partition sets and labels
  let X := SymmetricForm (ZMod p) r (j + 1)
  let 𝒯 : Finset (Finset (Fin u)) := Finset.univ.filter (fun T : Finset (Fin u) =>
    ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧ T.Nonempty)
  have huniv : (Finset.univ : Finset (Fin u)) ∈ 𝒯 := by
    simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sdiff_self, Finset.card_empty]
    exact ⟨by push_cast; positivity, Finset.univ_nonempty_iff.mpr ⟨⟨0, hu⟩⟩⟩
  let L : (i : Fin u) → X → SymmetricForm (ZMod p) r j := fun i => FieldGraphSeparation.labels (j := j) t i
  let g := GraphProfile.column L 𝒯 (j + 1)
  have hsep : ∀ x x' : X, x ≠ x' → ∃ y : GraphProfile.Columns X 𝒯, 1 ≤ |g y x - g y x'| := by
    intro x x' hne
    have hF : x - x' ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨T, hTc, hTne, hTrob⟩ := ht (x - x') hF
    have hT𝒯 : T ∈ 𝒯 := by simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hTc, hTne⟩
    refine ⟨(x, ⟨T, hT𝒯⟩), ?_⟩
    have h1 : g (x, ⟨T, hT𝒯⟩) x = 1 := by
      simp only [g, GraphProfile.column, PartitionGraph.distance_self, LogProfile.phi_zero]
    have hdist : ((j + 1 : ℕ) : ℕ∞) ≤ PartitionGraph.distance L T x' x := by
      unfold PartitionGraph.distance
      by_cases htop : (PartitionGraph.graph L T).edist x' x = ⊤
      · rw [htop]; exact le_top
      · obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
        have := FieldGraphSeparation.no_short_walk t T hTne x' x
          (fun a ha => hTrob a ha) w
        rw [← hw]
        exact_mod_cast this.le
    have h2 : g (x, ⟨T, hT𝒯⟩) x' = 0 := by
      simp only [g, GraphProfile.column]
      exact LogProfile.phi_eq_zero_of_le (Nat.succ_pos j) hdist
    rw [h1, h2]; norm_num
  -- the positive compression list
  set q := p ^ formDimension r j with hqdef
  have hq : 0 < q := pow_pos hp.pos _
  have hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q := by
    intro i
    calc Nat.card (Set.range (L i)) ≤ Nat.card (SymmetricForm (ZMod p) r j) :=
          Finite.card_subtype_le _
      _ = q := by rw [Nat.card_eq_fintype_card, h51e_card_form]
  have hs : 0 < s := by
    rw [hsdef]; unfold pivotSlots; exact Nat.ceil_pos.mpr (by positivity)
  have hsθ : 1 ≤ (s : ℝ) * θ := by
    have := Nat.le_ceil (1 / θ)
    have e : s = Nat.ceil (1 / θ) := rfl
    rw [e]
    rw [div_le_iff₀ hθ0] at this
    linarith
  have hprofile : Real.log 3 / Real.log (((j + 1 : ℕ) : ℝ) + 1) ≤ θ := by
    have hj := Nat.le_ceil (Real.exp (Real.log 3 / θ))
    have hlt : Real.exp (Real.log 3 / θ) < ((j + 1 : ℕ) : ℝ) + 1 := by
      have : (j : ℝ) = (Nat.ceil (Real.exp (Real.log 3 / θ)) : ℝ) := rfl
      push_cast; linarith
    have hlog := Real.log_lt_log (Real.exp_pos _) hlt
    rw [Real.log_exp] at hlog
    have hL : 0 < Real.log (((j + 1 : ℕ) : ℝ) + 1) := Real.log_pos (by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
    rw [div_le_iff₀ hL]
    rw [div_lt_iff₀ hθ0] at hlog
    linarith
  have hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) := by
    intro T hT; simp only [𝒯, Finset.mem_filter] at hT; exact hT.2.1
  haveI : Nonempty X := ⟨0⟩
  obtain ⟨P, hPne, hPcard, hPapprox⟩ := uniform_compression (X := X) (h := j + 1) (s := s) L hlabels 𝒯
    hu hq (Nat.succ_pos j) hs θ hθ0 hsθ hprofile hcomp
  -- signed differences
  let A : Finset (RealSpace X) := SignedCompression.differenceList P
  have hA : UniformApproximation g (6 * θ) A := by
    intro lam hlam
    simp only [l1Ball, Set.mem_setOf_eq, l1Norm] at hlam
    let lp : RealSpace (GraphProfile.Columns X 𝒯) := fun y => max (lam y) 0
    let ln : RealSpace (GraphProfile.Columns X 𝒯) := fun y => max (-lam y) 0
    have hsplit : ∀ y, |lam y| = lp y + ln y := by
      intro y; simp only [lp, ln]
      rcases le_total 0 (lam y) with h | h
      · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
    have hlp0 : ∀ y, 0 ≤ lp y := fun y => le_max_right _ _
    have hln0 : ∀ y, 0 ≤ ln y := fun y => le_max_right _ _
    have hsum : ∑ y, lp y + ∑ y, ln y ≤ 1 := by
      rw [← Finset.sum_add_distrib]; simp_rw [← hsplit]; exact hlam
    have hlp1 : ∑ y, lp y ≤ 1 := by linarith [Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => hln0 y)]
    have hln1 : ∑ y, ln y ≤ 1 := by linarith [Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => hlp0 y)]
    obtain ⟨a1, ha1, hc1⟩ := hPapprox lp hlp0 hlp1
    obtain ⟨a2, ha2, hc2⟩ := hPapprox ln hln0 hln1
    refine ⟨a1 - a2, ?_, ?_⟩
    · show a1 - a2 ∈ SignedCompression.differenceList P
      unfold SignedCompression.differenceList
      exact @Finset.mem_image_of_mem _ _ (fun a b => Classical.propDecidable (a = b)) _ _ (a1, a2)
        (Finset.mem_product.mpr ⟨ha1, ha2⟩)
    · intro x
      have hcc : columnCombination g lam x = columnCombination g lp x - columnCombination g ln x := by
        simp only [columnCombination, ← Finset.sum_sub_distrib, ← sub_mul]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        congr 1
        simp only [lp, ln]
        rcases le_total 0 (lam y) with h | h
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      have e1 := hc1 x
      have e2 := hc2 x
      rw [hcc]
      simp only [Pi.sub_apply]
      rw [abs_le] at e1 e2 ⊢
      constructor <;> linarith
  have hAQ : A.card ≤ P.card ^ 2 := by
    show (SignedCompression.differenceList P).card ≤ P.card ^ 2
    unfold SignedCompression.differenceList
    calc _ ≤ (P.product P).card := by convert Finset.card_image_le
      _ = P.card ^ 2 := by rw [show P.product P = P ×ˢ P from rfl, Finset.card_product, sq]
  have hQ : Real.log (P.card : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a)) := by
    have hQpos : 0 < P.card := Finset.card_pos.mpr hPne
    have := log_count_le_encodingCost (h := j + 1) (u := u) (q := q) (Q := P.card) (θ := θ)
      hu hq hθ0 hQpos (by simpa using hPcard)
    rw [hhj, show j + 1 - 1 = j by omega]
    have hq' : ((q : ℕ) : ℝ) = (p : ℝ) ^ formDimension r j := by rw [hqdef]; push_cast; rfl
    rw [hq'] at this
    exact this
  have hrows : Fintype.card X = p ^ formDimension r (compressionRadius a) := by
    rw [hhj]; exact h51e_card_form p r (j + 1)
  have hcolumns : Fintype.card X ≤ Fintype.card (GraphProfile.Columns X 𝒯) := by
    rw [Fintype.card_prod]
    have : 1 ≤ Fintype.card {T // T ∈ 𝒯} := Fintype.card_pos_iff.mpr ⟨⟨_, huniv⟩⟩
    nlinarith
  haveI : Nonempty (GraphProfile.Columns X 𝒯) := ⟨(0, ⟨_, huniv⟩)⟩
  exact entropyPair_of_matrix (X := X) (Y := GraphProfile.Columns X 𝒯) a ha r hr0 B hB p hp hpexp g
    hrows hcolumns hsep A hA P.card hAQ hQ

