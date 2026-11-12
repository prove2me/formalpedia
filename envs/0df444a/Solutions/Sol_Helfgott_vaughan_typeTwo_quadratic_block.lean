-- Prove2me | solution 1 for Helfgott.vaughan_typeTwo_quadratic_block
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T18:38:55.302934+00:00
-- url     : https://prove2.me/submissions/2117e85f-c843-46ad-bfdd-ff14202eadb6

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Data.Prod.Lex
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_Helfgott_WeightedCounting
import Definitions.Def_Helfgott_VaughanData
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
section
/- Rational-grid spacing proof adapted from accepted Prove2Me submission
968ef56d-d4b0-42b8-99aa-5a18c7253fab by marwahaha.
Parts derive from MathExtras and AnalyticNT, copyright (c) 2026 Gershon Bialer,
Apache 2.0. The spacing proof is retained, with a local namespace and phase
definition; unrelated exponential-sum interfaces are omitted. -/

open scoped BigOperators
namespace HelfgottQuadratic
noncomputable def perturbedPhase (a q : ℕ) (beta phi : ℝ) (j : ℕ) : ℝ :=
  (a : ℝ)*(j : ℝ)/(q : ℝ)+beta*(j : ℝ)+phi

theorem int_finset_card_le_of_mem_open_interval
    (z : Finset ℤ) (L U : ℝ) (r : ℕ)
    (hz : ∀ k ∈ z, L < (k : ℝ) ∧ (k : ℝ) < U)
    (hwidth : U - L ≤ (r : ℝ) + 1) :
    z.card ≤ r + 1 := by
  classical
  by_cases hze : z = ∅
  · simp [hze]
  have hznon : z.Nonempty := Finset.nonempty_iff_ne_empty.mpr hze
  let m : ℤ := z.min' hznon
  let M : ℤ := z.max' hznon
  have hm_mem : m ∈ z := Finset.min'_mem z hznon
  have hM_mem : M ∈ z := Finset.max'_mem z hznon
  have hsub : z ⊆ Finset.Icc m M := by
    intro k hk
    simp only [Finset.mem_Icc]
    exact ⟨Finset.min'_le z k hk, Finset.le_max' z k hk⟩
  have hcard : z.card ≤ (M + 1 - m).toNat := by
    have h := Finset.card_le_card hsub
    simpa [Int.card_Icc] using h
  have hgapR : (M : ℝ) - (m : ℝ) < (r : ℝ) + 1 := by
    have hm := (hz m hm_mem).1
    have hM := (hz M hM_mem).2
    linarith
  have hgapZ : M - m ≤ (r : ℤ) := by
    have hgapZlt : M - m < (r : ℤ) + 1 := by exact_mod_cast hgapR
    omega
  have htoNat : (M + 1 - m).toNat ≤ r + 1 := by
    rw [Int.toNat_le]
    exact_mod_cast (show M + 1 - m ≤ (r : ℤ) + 1 by omega)
  exact hcard.trans htoNat
theorem perturbed_residual_card_le
    {ι : Type*} [DecidableEq ι] (q r : ℕ) (hq : 0 < q)
    (s : Finset ι) (tag : ι → ℤ) (v err : ι → ℝ)
    (c Elo Ehi : ℝ)
    (hinj : Set.InjOn tag (↑s : Set ι))
    (hv : ∀ i ∈ s, |v i| < (r : ℝ) / (2 * (q : ℝ)))
    (herr : ∀ i ∈ s, Elo ≤ err i ∧ err i ≤ Ehi)
    (hspan : Ehi - Elo < 1)
    (htag : ∀ i ∈ s, (tag i : ℝ) = (q : ℝ) * v i - c - err i) :
    s.card ≤ r + 1 := by
  classical
  let delta : ℝ := (r : ℝ) / (2 * (q : ℝ))
  let L : ℝ := -(q : ℝ) * delta - c - Ehi
  let U : ℝ := (q : ℝ) * delta - c - Elo
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hscale : 2 * (q : ℝ) * delta = (r : ℝ) := by
    dsimp [delta]
    field_simp
  have hmem : ∀ k ∈ s.image tag, L < (k : ℝ) ∧ (k : ℝ) < U := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    have hv' := abs_lt.mp (hv i hi)
    have he := herr i hi
    rw [htag i hi]
    dsimp [L, U, delta] at hv' ⊢
    constructor <;> nlinarith
  have hwidth : U - L ≤ (r : ℝ) + 1 := by
    dsimp [L, U]
    nlinarith
  have hpack := int_finset_card_le_of_mem_open_interval
    (s.image tag) L U r hmem hwidth
  rwa [Finset.card_image_of_injOn hinj] at hpack
noncomputable def perturbedPhaseResidual
    (a q : ℕ) (beta phi : ℝ) (j : ℕ) : ℝ :=
  perturbedPhase a q beta phi j - round (perturbedPhase a q beta phi j)
noncomputable def perturbedPhaseTag
    (a q : ℕ) (beta phi : ℝ) (j : ℕ) : ℤ :=
  (a * j : ℕ) - (q : ℤ) * round (perturbedPhase a q beta phi j)
noncomputable def perturbedPhaseError (q : ℕ) (beta : ℝ) (j : ℕ) : ℝ :=
  (q : ℝ) * beta * (j : ℝ)
theorem coprime_lifted_tags_injOn
    (a q : ℕ) (R : ℕ → ℤ) (haq : Nat.Coprime a q) :
    Set.InjOn (fun j : ℕ => ((a * j : ℕ) : ℤ) - (q : ℤ) * R j)
      (↑(Finset.range q) : Set ℕ) := by
  intro j hj k hk h
  have hcast := congrArg (fun z : ℤ => (z : ZMod q)) h
  push_cast at hcast
  simp at hcast
  have hmod : a * j ≡ a * k [MOD q] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul] using hcast
  have hjk : j ≡ k [MOD q] :=
    hmod.cancel_left_of_coprime
      (by simpa [Nat.Coprime, Nat.gcd_comm] using haq)
  rw [Nat.ModEq] at hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at hjk
  exact hjk
theorem perturbedPhaseTag_injOn
    (a q : ℕ) (beta phi : ℝ) (haq : Nat.Coprime a q) :
    Set.InjOn (perturbedPhaseTag a q beta phi)
      (↑(Finset.range q) : Set ℕ) := by
  exact coprime_lifted_tags_injOn a q
    (fun j => round (perturbedPhase a q beta phi j)) haq
theorem perturbedPhaseTag_eq
    (a q : ℕ) (beta phi : ℝ) (hq : 0 < q) (j : ℕ) :
    ((perturbedPhaseTag a q beta phi j : ℤ) : ℝ) =
      (q : ℝ) * perturbedPhaseResidual a q beta phi j -
        (q : ℝ) * phi - perturbedPhaseError q beta j := by
  unfold perturbedPhaseTag perturbedPhaseResidual perturbedPhaseError perturbedPhase
  push_cast
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hqR]
  ring
theorem perturbed_error_span_lt_one
    (q : ℕ) (hq : 2 ≤ q) (beta : ℝ)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (q : ℝ) * |beta| * ((q : ℝ) - 1) < 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (show 1 ≤ q by omega)
  have hqm : (0 : ℝ) ≤ (q : ℝ) - 1 := sub_nonneg.mpr hq1R
  calc
    (q : ℝ) * |beta| * ((q : ℝ) - 1)
        ≤ (q : ℝ) * (1 / (q : ℝ) ^ 2) * ((q : ℝ) - 1) := by
          gcongr
    _ = ((q : ℝ) - 1) / (q : ℝ) := by field_simp
    _ < 1 := (div_lt_one hqR).2 (by linarith)
theorem perturbed_grid_sublevel_card_le
    (a q r : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (beta phi : ℝ) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ((Finset.range q).filter fun j =>
      |perturbedPhaseResidual a q beta phi j| <
        (r : ℝ) / (2 * (q : ℝ))).card ≤ r + 1 := by
  classical
  let s : Finset ℕ := (Finset.range q).filter fun j =>
    |perturbedPhaseResidual a q beta phi j| <
      (r : ℝ) / (2 * (q : ℝ))
  have hq0 : 0 < q := by omega
  have hinj : Set.InjOn (perturbedPhaseTag a q beta phi)
      (↑s : Set ℕ) :=
    (perturbedPhaseTag_injOn a q beta phi haq).mono (by
      intro j hj
      exact (Finset.mem_filter.mp hj).1)
  have hspan0 := perturbed_error_span_lt_one q hq beta hbeta
  by_cases hb : 0 ≤ beta
  · let Ehi : ℝ := (q : ℝ) * beta * ((q : ℝ) - 1)
    have herr : ∀ j ∈ s, 0 ≤ perturbedPhaseError q beta j ∧
        perturbedPhaseError q beta j ≤ Ehi := by
      intro j hj
      have hjq : j < q := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have hjplus : j + 1 ≤ q := by omega
      have hjplusR : ((j + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hjplus
      have hjle : (j : ℝ) ≤ (q : ℝ) - 1 := by
        norm_num at hjplusR ⊢
        linarith
      dsimp [perturbedPhaseError, Ehi]
      constructor
      · positivity
      · exact mul_le_mul_of_nonneg_left hjle
          (mul_nonneg (by positivity) hb)
    have hspan : Ehi - 0 < 1 := by
      dsimp [Ehi]
      rw [abs_of_nonneg hb] at hspan0
      simpa using hspan0
    have hv : ∀ j ∈ s, |perturbedPhaseResidual a q beta phi j| <
        (r : ℝ) / (2 * (q : ℝ)) := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hc := perturbed_residual_card_le q r hq0 s
      (perturbedPhaseTag a q beta phi)
      (perturbedPhaseResidual a q beta phi)
      (perturbedPhaseError q beta) ((q : ℝ) * phi) 0 Ehi
      hinj hv herr hspan
      (fun j hj => perturbedPhaseTag_eq a q beta phi hq0 j)
    exact hc
  · have hb' : beta ≤ 0 := le_of_not_ge hb
    let Elo : ℝ := (q : ℝ) * beta * ((q : ℝ) - 1)
    have herr : ∀ j ∈ s, Elo ≤ perturbedPhaseError q beta j ∧
        perturbedPhaseError q beta j ≤ 0 := by
      intro j hj
      have hjq : j < q := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have hjplus : j + 1 ≤ q := by omega
      have hjplusR : ((j + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hjplus
      have hjle : (j : ℝ) ≤ (q : ℝ) - 1 := by
        norm_num at hjplusR ⊢
        linarith
      dsimp [perturbedPhaseError, Elo]
      constructor
      · exact mul_le_mul_of_nonpos_left hjle
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hb')
      · exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hb') hj0
    have hspan : 0 - Elo < 1 := by
      dsimp [Elo]
      rw [abs_of_nonpos hb'] at hspan0
      nlinarith
    have hv : ∀ j ∈ s, |perturbedPhaseResidual a q beta phi j| <
        (r : ℝ) / (2 * (q : ℝ)) := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hc := perturbed_residual_card_le q r hq0 s
      (perturbedPhaseTag a q beta phi)
      (perturbedPhaseResidual a q beta phi)
      (perturbedPhaseError q beta) ((q : ℝ) * phi) Elo 0
      hinj hv herr hspan
      (fun j hj => perturbedPhaseTag_eq a q beta phi hq0 j)
    exact hc
noncomputable def distancePoint (d : ℕ → ℝ) (j : ℕ) : ℝ ×ₗ ℕ :=
  toLex (d j, j)
theorem distancePoint_injective (d : ℕ → ℝ) :
    Function.Injective (distancePoint d) := by
  intro j k h
  exact congrArg (fun x : ℝ ×ₗ ℕ => (ofLex x).2) h
theorem distancePoint_image_card (q : ℕ) (d : ℕ → ℝ) :
    ((Finset.range q).image (distancePoint d)).card = q := by
  rw [Finset.card_image_of_injective _ (distancePoint_injective d),
    Finset.card_range]
noncomputable def enumDistancePoint (q : ℕ) (d : ℕ → ℝ) :
    Fin q → ℝ ×ₗ ℕ :=
  (((Finset.range q).image (distancePoint d)).orderEmbOfFin
    (distancePoint_image_card q d))
theorem enumDistancePoint_mem (q : ℕ) (d : ℕ → ℝ) (i : Fin q) :
    enumDistancePoint q d i ∈
      (Finset.range q).image (distancePoint d) := by
  exact Finset.orderEmbOfFin_mem _ _ i
theorem enumDistancePoint_injective (q : ℕ) (d : ℕ → ℝ) :
    Function.Injective (enumDistancePoint q d) := by
  exact (((Finset.range q).image (distancePoint d)).orderEmbOfFin
    (distancePoint_image_card q d)).injective
noncomputable def distancePointIndex
    (q : ℕ) (d : ℕ → ℝ) (j : ℕ) (hj : j < q) : Fin q :=
  (((Finset.range q).image (distancePoint d)).orderIsoOfFin
    (distancePoint_image_card q d)).symm
      ⟨distancePoint d j,
        Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩⟩
theorem enumDistancePoint_distancePointIndex
    (q : ℕ) (d : ℕ → ℝ) (j : ℕ) (hj : j < q) :
    enumDistancePoint q d (distancePointIndex q d j hj) =
      distancePoint d j := by
  exact congrArg Subtype.val
    ((((Finset.range q).image (distancePoint d)).orderIsoOfFin
      (distancePoint_image_card q d)).apply_symm_apply
        ⟨distancePoint d j,
          Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩⟩)
theorem enumDistancePoint_mono
    (q : ℕ) (d : ℕ → ℝ) {i k : Fin q} (hik : i ≤ k) :
    enumDistancePoint q d i ≤ enumDistancePoint q d k := by
  exact (((Finset.range q).image (distancePoint d)).orderEmbOfFin
    (distancePoint_image_card q d)).monotone hik
theorem distancePoint_filter_card
    (q : ℕ) (d : ℕ → ℝ) (delta : ℝ) :
    (((Finset.range q).image (distancePoint d)).filter fun x =>
      (ofLex x).1 < delta).card =
        ((Finset.range q).filter fun j => d j < delta).card := by
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ (distancePoint_injective d)]
  rfl
theorem distance_prefix_card_le_filter_card
    (q : ℕ) (d : ℕ → ℝ) (i : Fin q)
    (delta : ℝ) (hi : (ofLex (enumDistancePoint q d i)).1 < delta) :
    i.val + 1 ≤
      (((Finset.range q).image (distancePoint d)).filter fun x =>
        (ofLex x).1 < delta).card := by
  let pref : Finset (ℝ ×ₗ ℕ) :=
    (Finset.Iic i).image (enumDistancePoint q d)
  have hsub : pref ⊆
      (((Finset.range q).image (distancePoint d)).filter fun x =>
        (ofLex x).1 < delta) := by
    intro x hx
    obtain ⟨k, hki, rfl⟩ := Finset.mem_image.mp hx
    have hle : k ≤ i := Finset.mem_Iic.mp hki
    have hpair := enumDistancePoint_mono q d hle
    have hfirst : (ofLex (enumDistancePoint q d k)).1 ≤
        (ofLex (enumDistancePoint q d i)).1 := by
      rw [Prod.Lex.le_iff] at hpair
      rcases hpair with hlt | heq
      · exact hlt.le
      · exact heq.1.le
    exact Finset.mem_filter.mpr
      ⟨enumDistancePoint_mem q d k, lt_of_le_of_lt hfirst hi⟩
  have hcard := Finset.card_le_card hsub
  have hpref : pref.card = i.val + 1 := by
    dsimp [pref]
    rw [Finset.card_image_of_injective _
      (enumDistancePoint_injective q d)]
    simp
  simpa [hpref] using hcard
noncomputable def distancePointIndexTotal
    (q : ℕ) (hq : 0 < q) (d : ℕ → ℝ) (j : ℕ) : Fin q :=
  if hj : j < q then distancePointIndex q d j hj else ⟨0, hq⟩
theorem distancePointIndexTotal_eq
    (q : ℕ) (hq : 0 < q) (d : ℕ → ℝ) (j : ℕ) (hj : j < q) :
    distancePointIndexTotal q hq d j = distancePointIndex q d j hj := by
  simp only [distancePointIndexTotal, dif_pos hj]
theorem distancePointIndexTotal_injectiveOn
    (q : ℕ) (hq : 0 < q) (d : ℕ → ℝ) :
    Set.InjOn (distancePointIndexTotal q hq d)
      (↑(Finset.range q) : Set ℕ) := by
  intro j hj k hk hidx
  have hjq : j < q := by simpa using hj
  have hkq : k < q := by simpa using hk
  rw [distancePointIndexTotal_eq q hq d j hjq,
    distancePointIndexTotal_eq q hq d k hkq] at hidx
  have hpoint : distancePoint d j = distancePoint d k := by
    rw [← enumDistancePoint_distancePointIndex q d j hjq,
      ← enumDistancePoint_distancePointIndex q d k hkq, hidx]
  exact distancePoint_injective d hpoint
theorem distancePointIndex_lower
    (q : ℕ) (_hq : 2 ≤ q) (d : ℕ → ℝ)
    (hcount : ∀ r : ℕ,
      ((Finset.range q).filter fun j =>
        d j < (r : ℝ) / (2 * (q : ℝ))).card ≤ r + 1)
    (j : ℕ) (hjq : j < q)
    (hi : 2 ≤ (distancePointIndex q d j hjq).val) :
    ((distancePointIndex q d j hjq).val - 1 : ℕ) /
        (2 * (q : ℝ)) ≤ d j := by
  let i := distancePointIndex q d j hjq
  by_contra hnot
  have hdlt : d j < ((i.val - 1 : ℕ) : ℝ) /
      (2 * (q : ℝ)) := lt_of_not_ge hnot
  have henumlt : (ofLex (enumDistancePoint q d i)).1 <
      ((i.val - 1 : ℕ) : ℝ) / (2 * (q : ℝ)) := by
    rw [enumDistancePoint_distancePointIndex q d j hjq]
    exact hdlt
  have hlo := distance_prefix_card_le_filter_card q d i
    (((i.val - 1 : ℕ) : ℝ) / (2 * (q : ℝ))) henumlt
  rw [distancePoint_filter_card] at hlo
  have hhi := hcount (i.val - 1)
  omega
theorem rank_certificate_of_sublevel_card
    (q : ℕ) (hq : 2 ≤ q) (d : ℕ → ℝ)
    (hcount : ∀ r : ℕ,
      ((Finset.range q).filter fun j =>
        d j < (r : ℝ) / (2 * (q : ℝ))).card ≤ r + 1) :
    ∃ (e : Finset ℕ) (rank : ℕ → ℕ),
      e ⊆ Finset.range q ∧ e.card ≤ 2 ∧
      Set.InjOn rank (↑(Finset.range q \ e) : Set ℕ) ∧
      ∀ j ∈ Finset.range q \ e,
        rank j ∈ Finset.Ico 1 (q - 1) ∧
          (rank j : ℝ) / (2 * (q : ℝ)) ≤ d j := by
  classical
  have hq0 : 0 < q := by omega
  let idx : ℕ → Fin q := distancePointIndexTotal q hq0 d
  let e : Finset ℕ := (Finset.range q).filter fun j => (idx j).val < 2
  let rank : ℕ → ℕ := fun j => (idx j).val - 1
  have hidx : Set.InjOn idx (↑(Finset.range q) : Set ℕ) := by
    dsimp [idx]
    exact distancePointIndexTotal_injectiveOn q hq0 d
  have he_sub : e ⊆ Finset.range q := Finset.filter_subset _ _
  have he_card : e.card ≤ 2 := by
    let f : ℕ → ℕ := fun j => (idx j).val
    have hf_inj : Set.InjOn f (↑e : Set ℕ) := by
      intro j hj k hk heq
      apply hidx (he_sub hj) (he_sub hk)
      apply Fin.ext
      exact heq
    have himage : e.image f ⊆ Finset.range 2 := by
      intro n hn
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
    calc
      e.card = (e.image f).card :=
        (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ (Finset.range 2).card := Finset.card_le_card himage
      _ = 2 := Finset.card_range 2
  refine ⟨e, rank, he_sub, he_card, ?_, ?_⟩
  · intro j hj k hk hrank
    have hj_range : j ∈ Finset.range q := (Finset.mem_sdiff.mp hj).1
    have hk_range : k ∈ Finset.range q := (Finset.mem_sdiff.mp hk).1
    have hj_not : j ∉ e := (Finset.mem_sdiff.mp hj).2
    have hk_not : k ∉ e := (Finset.mem_sdiff.mp hk).2
    have hj2 : 2 ≤ (idx j).val := by
      dsimp [e] at hj_not
      simp only [Finset.mem_filter, hj_range, true_and, not_lt] at hj_not
      exact hj_not
    have hk2 : 2 ≤ (idx k).val := by
      dsimp [e] at hk_not
      simp only [Finset.mem_filter, hk_range, true_and, not_lt] at hk_not
      exact hk_not
    apply hidx hj_range hk_range
    apply Fin.ext
    dsimp [rank] at hrank
    omega
  · intro j hj
    have hj_range : j ∈ Finset.range q := (Finset.mem_sdiff.mp hj).1
    have hjq : j < q := Finset.mem_range.mp hj_range
    have hj_not : j ∉ e := (Finset.mem_sdiff.mp hj).2
    have hj2 : 2 ≤ (idx j).val := by
      dsimp [e] at hj_not
      simp only [Finset.mem_filter, hj_range, true_and, not_lt] at hj_not
      exact hj_not
    have hidxeq : idx j = distancePointIndex q d j hjq := by
      dsimp [idx]
      exact distancePointIndexTotal_eq q hq0 d j hjq
    have hdist := distancePointIndex_lower q hq d hcount j hjq (by
      rwa [← hidxeq])
    constructor
    · simp only [Finset.mem_Ico]
      dsimp [rank]
      have hidxlt : (idx j).val < q := (idx j).isLt
      omega
    · dsimp [rank]
      rwa [← hidxeq] at hdist
theorem abs_sin_pi_eq_sin_pi_abs_sub_round (x : ℝ) :
    |Real.sin (Real.pi * x)| =
      Real.sin (Real.pi * |x - round x|) := by
  let y : ℝ := x - round x
  have hxy : x = y + (round x : ℝ) := by
    dsimp [y]
    ring
  have harg : Real.pi * x =
      Real.pi * y + (round x : ℝ) * Real.pi := by
    conv_lhs => rw [hxy]
    ring
  rw [harg, Real.sin_add_int_mul_pi]
  have hsign : |((-1 : ℝ) ^ (round x))| = 1 := by simp
  rw [abs_mul, hsign, one_mul]
  have hy : |y| ≤ 1 / 2 := by
    dsimp [y]
    exact abs_sub_round x
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hpiy : |Real.pi * y| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg hpi]
    nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpiy]
  rw [abs_mul, abs_of_nonneg hpi]
theorem perturbed_grid_sine_rank_certificate
    (a q : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (beta phi : ℝ) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ∃ (e : Finset ℕ) (rank : ℕ → ℕ),
      e ⊆ Finset.range q ∧ e.card ≤ 2 ∧
      Set.InjOn rank (↑(Finset.range q \ e) : Set ℕ) ∧
      (∀ j ∈ Finset.range q \ e,
        rank j ∈ Finset.Ico 1 (q - 1)) ∧
      ∀ j ∈ Finset.range q \ e,
        Real.sin (Real.pi * (rank j : ℝ) / (2 * (q : ℝ))) ≤
          |Real.sin (Real.pi * perturbedPhase a q beta phi j)| := by
  classical
  have hcount : ∀ r : ℕ,
      ((Finset.range q).filter fun j =>
        |perturbedPhaseResidual a q beta phi j| <
          (r : ℝ) / (2 * (q : ℝ))).card ≤ r + 1 := by
    intro r
    exact perturbed_grid_sublevel_card_le a q r hq haq beta phi hbeta
  obtain ⟨e, rank, hes, hecard, hinj, hrank⟩ :=
    rank_certificate_of_sublevel_card q hq
      (fun j => |perturbedPhaseResidual a q beta phi j|) hcount
  refine ⟨e, rank, hes, hecard, hinj,
    (fun j hj => (hrank j hj).1), ?_⟩
  intro j hj
  have hr := hrank j hj
  have hres : |perturbedPhaseResidual a q beta phi j| ≤ 1 / 2 := by
    unfold perturbedPhaseResidual
    exact abs_sub_round (perturbedPhase a q beta phi j)
  have hz0 : (0 : ℝ) ≤ (rank j : ℝ) / (2 * (q : ℝ)) := by
    positivity
  have hleft : -(Real.pi / 2) ≤
      Real.pi * ((rank j : ℝ) / (2 * (q : ℝ))) := by
    have hnon : 0 ≤ Real.pi * ((rank j : ℝ) / (2 * (q : ℝ))) :=
      mul_nonneg Real.pi_pos.le hz0
    linarith [Real.pi_pos]
  have hy : Real.pi * |perturbedPhaseResidual a q beta phi j| ≤
      Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hxy : Real.pi * ((rank j : ℝ) / (2 * (q : ℝ))) ≤
      Real.pi * |perturbedPhaseResidual a q beta phi j| :=
    mul_le_mul_of_nonneg_left hr.2 Real.pi_pos.le
  have hsine := Real.sin_le_sin_of_le_of_le_pi_div_two hleft hy hxy
  rw [abs_sin_pi_eq_sin_pi_abs_sub_round]
  change Real.sin (Real.pi * (rank j : ℝ) / (2 * (q : ℝ))) ≤
    Real.sin (Real.pi * |perturbedPhaseResidual a q beta phi j|)
  simpa only [div_eq_mul_inv, mul_assoc] using hsine

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem reciprocal_square_tail (K N : ℕ) (hK : 0 < K) :
    (∑ j ∈ range N, 1 / ((K+j+1:ℕ):ℝ)^2) ≤
      1/(K:ℝ)-1/((K+N:ℕ):ℝ) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hKN : (0:ℝ) < K+N := by positivity
    have hstep : 1/((K:ℝ)+N+1)^2 ≤ 1/((K:ℝ)+N)-1/((K:ℝ)+N+1) := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < ((K:ℝ)+N+1)^2)).mpr
      field_simp
      nlinarith
    push_cast at ih ⊢
    rw [← add_assoc]
    linarith

theorem reciprocal_square_sum (N : ℕ) :
    (∑ j ∈ range N, 1 / ((j+1:ℕ):ℝ)^2) ≤ 2 := by
  cases N with
  | zero => simp
  | succ N =>
    rw [sum_range_succ']
    have h := reciprocal_square_tail 1 N (by omega)
    have heq : (∑ j ∈ range N, 1 / ((j+1+1:ℕ):ℝ)^2) =
        ∑ j ∈ range N, 1 / ((1+j+1:ℕ):ℝ)^2 := by
      apply sum_congr rfl
      intro j hj
      congr 3 <;> omega
    rw [heq]
    norm_num at h ⊢
    have hn : (0:ℝ) ≤ (1+(N:ℝ))⁻¹ := by positivity
    linarith

theorem capped_square_split (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (N K : ℕ) (hK : 0 < K) :
    (∑ j ∈ range N, min A (D/((j+1:ℕ):ℝ)^2)) ≤ A*K+D/K := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have hhead : ∀ M : ℕ, (∑ j ∈ range M, min A (D/((j+1:ℕ):ℝ)^2)) ≤ A*M := by
    intro M
    calc
      _ ≤ ∑ _j ∈ range M, A := sum_le_sum (fun _ _ => min_le_left _ _)
      _ = A*M := by simp [mul_comm]
  by_cases hNK : N ≤ K
  · exact (hhead N).trans ((mul_le_mul_of_nonneg_left (by exact_mod_cast hNK) hA).trans
      (le_add_of_nonneg_right (div_nonneg hD hKR.le)))
  · have hKN : K ≤ N := by omega
    obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hKN
    rw [sum_range_add]
    have htail : (∑ j ∈ range M, min A (D/((K+j+1:ℕ):ℝ)^2)) ≤ D/K := by
      calc
        _ ≤ ∑ j ∈ range M, D/((K+j+1:ℕ):ℝ)^2 :=
          sum_le_sum (fun _ _ => min_le_right _ _)
        _ = D*∑ j ∈ range M, 1/((K+j+1:ℕ):ℝ)^2 := by rw [mul_sum]; simp [div_eq_mul_inv]
        _ ≤ D*(1/(K:ℝ)-1/((K+M:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left (reciprocal_square_tail K M hK) hD
        _ ≤ D/K := by
          have h : (0:ℝ) ≤ D/((K+M:ℕ):ℝ) := by positivity
          simpa [mul_sub,div_eq_mul_inv] using sub_le_self (D*(K:ℝ)⁻¹) h
    exact add_le_add (hhead K) htail

theorem capped_square_sum_sqrt (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (N : ℕ) :
    (∑ j ∈ range N, min A (D/((j+1:ℕ):ℝ)^2)) ≤ A+2*Real.sqrt (A*D) := by
  by_cases hAz : A = 0
  · subst A
    simp only [zero_mul,Real.sqrt_zero,mul_zero,add_zero]
    exact sum_nonpos (fun j hj => min_le_left _ _)
  by_cases hDz : D = 0
  · subst D
    simp [min_eq_right hA,hA]
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
  let s := Real.sqrt (D/A)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hDp hAp)
  have hs2 : s^2 = D/A := Real.sq_sqrt (by positivity)
  have hDs : D = A*s^2 := by apply (eq_div_iff hAz).mp at hs2; nlinarith [hs2]
  have hroot : Real.sqrt (A*D) = A*s := by
    rw [hDs, show A*(A*s^2) = (A*s)^2 by ring, Real.sqrt_sq (by positivity)]
  let K := ⌈s⌉₊
  have hK : 0 < K := Nat.ceil_pos.mpr hs
  have hsK : s ≤ (K:ℝ) := Nat.le_ceil s
  have hKs : (K:ℝ) ≤ s+1 := (Nat.ceil_lt_add_one hs.le).le
  calc
    _ ≤ A*K+D/K := capped_square_split A D hA hD N K hK
    _ ≤ A*(s+1)+D/s := add_le_add (mul_le_mul_of_nonneg_left hKs hA)
      (div_le_div_of_nonneg_left hD hs hsK)
    _ = A+2*Real.sqrt (A*D) := by rw [hroot,hDs]; field_simp; ring

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

noncomputable def safeCappedSquare (A C phase : ℝ) : ℝ :=
  if Real.sin phase = 0 then A else min A (C/(Real.sin phase)^2)

theorem safeCappedSquare_nonneg (A C phase : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    0 ≤ safeCappedSquare A C phase := by
  unfold safeCappedSquare
  split_ifs
  · exact hA
  · exact le_min hA (div_nonneg hC (sq_nonneg _))

theorem safeCappedSquare_le_cap (A C phase : ℝ) :
    safeCappedSquare A C phase ≤ A := by
  unfold safeCappedSquare
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem quadratic_block_bound_of_rank_certificate
    (q : ℕ) (hq : 2 ≤ q) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (s e : Finset ℕ) (rank : ℕ → ℕ) (phase : ℕ → ℝ)
    (hes : e ⊆ s) (hecard : e.card ≤ 2)
    (hrange : ∀ n ∈ s \ e, rank n ∈ Finset.Ico 1 (q-1))
    (hinj : Set.InjOn rank (↑(s \ e) : Set ℕ))
    (hsep : ∀ n ∈ s \ e,
      Real.sin (Real.pi*(rank n:ℝ)/(2*(q:ℝ))) ≤ |Real.sin (phase n)|) :
    (∑ n ∈ s, safeCappedSquare A C (phase n)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by
  classical
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  let gridTerm : ℕ → ℝ := fun j => min A (C*(q:ℝ)^2/((j+1:ℕ):ℝ)^2)
  let idx : ℕ → ℕ := fun n => rank n-1
  have hidx : Set.InjOn idx (↑(s \ e) : Set ℕ) := by
    intro n hn m hm hnm
    apply hinj hn hm
    have hn1 := (mem_Ico.mp (hrange n hn)).1
    have hm1 := (mem_Ico.mp (hrange m hm)).1
    dsimp [idx] at hnm
    omega
  have hsub : (s \ e).image idx ⊆ range q := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
    have hr := mem_Ico.mp (hrange n hn)
    simp only [mem_range,idx]
    omega
  have hpoint : ∀ n ∈ s \ e, safeCappedSquare A C (phase n) ≤ gridTerm (idx n) := by
    intro n hn
    have hr := mem_Ico.mp (hrange n hn)
    have hrp : (0:ℝ) < rank n := by exact_mod_cast hr.1
    have hrq : (rank n:ℝ) ≤ q := by exact_mod_cast (show rank n ≤ q by omega)
    have hangle : Real.pi*(rank n:ℝ)/(2*(q:ℝ)) ≤ Real.pi/2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(q:ℝ))).mpr
      nlinarith [Real.pi_pos]
    have hlinear : (rank n:ℝ)/(q:ℝ) ≤ Real.sin (Real.pi*(rank n:ℝ)/(2*(q:ℝ))) := by
      have hh := Real.mul_le_sin (by positivity : (0:ℝ) ≤ Real.pi*(rank n:ℝ)/(2*(q:ℝ))) hangle
      convert hh using 1 <;> field_simp <;> ring
    have hdist := hlinear.trans (hsep n hn)
    have hsin : 0 < |Real.sin (phase n)| := (div_pos hrp hqR).trans_le hdist
    have hne : Real.sin (phase n) ≠ 0 := abs_pos.mp hsin
    have hsquare : ((rank n:ℝ)/(q:ℝ))^2 ≤ (Real.sin (phase n))^2 := by
      have hh := mul_self_le_mul_self (div_nonneg hrp.le hqR.le) hdist
      simpa [sq_abs,pow_two] using hh
    have hdiv : C/(Real.sin (phase n))^2 ≤ C*(q:ℝ)^2/(rank n:ℝ)^2 := by
      calc
        _ ≤ C/((rank n:ℝ)/(q:ℝ))^2 :=
          div_le_div_of_nonneg_left hC (sq_pos_of_pos (div_pos hrp hqR)) hsquare
        _ = _ := by field_simp
    have hi : idx n+1 = rank n := by dsimp [idx]; omega
    simp only [safeCappedSquare,if_neg hne,gridTerm,hi]
    exact min_le_min_left A hdiv
  have hnonexceptional : (∑ n ∈ s \ e, safeCappedSquare A C (phase n)) ≤ ∑ j ∈ range q, gridTerm j := by
    calc
      _ ≤ ∑ n ∈ s \ e, gridTerm (idx n) := sum_le_sum hpoint
      _ = ∑ j ∈ (s \ e).image idx, gridTerm j := (sum_image hidx).symm
      _ ≤ ∑ j ∈ range q, gridTerm j := sum_le_sum_of_subset_of_nonneg hsub
        (fun j hj hnot => le_min hA (by positivity))
  have hexc : (∑ n ∈ e, safeCappedSquare A C (phase n)) ≤ 2*A := by
    calc
      _ ≤ ∑ _n ∈ e, A := sum_le_sum (fun n hn => safeCappedSquare_le_cap _ _ _)
      _ = (e.card:ℝ)*A := by simp
      _ ≤ 2*A := mul_le_mul_of_nonneg_right (by exact_mod_cast hecard) hA
  have hgrid1 : (∑ j ∈ range q, gridTerm j) ≤ 2*C*(q:ℝ)^2 := by
    calc
      _ ≤ ∑ j ∈ range q, C*(q:ℝ)^2/((j+1:ℕ):ℝ)^2 := sum_le_sum (fun j hj => min_le_right _ _)
      _ = (C*(q:ℝ)^2)*(∑ j ∈ range q, 1/((j+1:ℕ):ℝ)^2) := by rw [mul_sum]; simp [div_eq_mul_inv]
      _ ≤ (C*(q:ℝ)^2)*2 := mul_le_mul_of_nonneg_left (reciprocal_square_sum q) (by positivity)
      _ = _ := by ring
  have hroot : Real.sqrt (A*(C*(q:ℝ)^2)) = (q:ℝ)*Real.sqrt (A*C) := by
    rw [show A*(C*(q:ℝ)^2) = (A*C)*(q:ℝ)^2 by ring,
      Real.sqrt_mul (mul_nonneg hA hC),Real.sqrt_sq (Nat.cast_nonneg q)]
    ring
  have hgrid2 : (∑ j ∈ range q, gridTerm j) ≤ A+2*(q:ℝ)*Real.sqrt (A*C) := by
    have hh := capped_square_sum_sqrt A (C*(q:ℝ)^2) hA (by positivity) q
    rw [hroot] at hh
    simpa [gridTerm,mul_assoc] using hh
  calc
    _ = (∑ n ∈ s \ e, safeCappedSquare A C (phase n))+
        ∑ n ∈ e, safeCappedSquare A C (phase n) := (sum_sdiff hes).symm
    _ ≤ (∑ j ∈ range q, gridTerm j)+2*A := add_le_add hnonexceptional hexc
    _ ≤ min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C))+2*A :=
      add_le_add (le_min hgrid1 hgrid2) le_rfl
    _ = _ := by ring

theorem perturbed_grid_quadratic_bound (a q : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (beta phi A C : ℝ) (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ range q, safeCappedSquare A C (Real.pi*perturbedPhase a q beta phi j)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by
  obtain ⟨e,rank,hes,hecard,hinj,hrange,hsep⟩ :=
    perturbed_grid_sine_rank_certificate a q hq haq beta phi hbeta
  exact quadratic_block_bound_of_rank_certificate q hq A C hA hC (range q) e rank
    (fun j => Real.pi*perturbedPhase a q beta phi j) hes hecard hrange hinj hsep

theorem quadratic_rational_block_nat (a q N : ℕ) (hq : 2 ≤ q) (haq : Nat.Coprime a q)
    (hN : N ≤ q) (alpha beta theta M A C : ℝ)
    (halpha : alpha = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ range N, safeCappedSquare A C (Real.pi*alpha*(M+(j:ℝ))+theta)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by
  have hphase : ∀ j : ℕ, Real.pi*alpha*(M+(j:ℝ))+theta =
      Real.pi*perturbedPhase a q beta (alpha*M+theta/Real.pi) j := by
    intro j
    unfold perturbedPhase
    rw [halpha]
    field_simp
    ring
  simp_rw [hphase]
  refine (sum_le_sum_of_subset_of_nonneg (range_mono hN)
    (fun j hj hn => safeCappedSquare_nonneg _ _ _ hA hC)).trans ?_
  exact perturbed_grid_quadratic_bound a q hq haq beta _ A C hbeta hA hC

theorem safeCappedSquare_neg (A C phase : ℝ) :
    safeCappedSquare A C (-phase) = safeCappedSquare A C phase := by
  simp [safeCappedSquare]

theorem quadratic_rational_block_int (a : ℤ) (q N : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (hN : N ≤ q) (alpha beta theta M A C : ℝ)
    (halpha : alpha = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ range N, safeCappedSquare A C (Real.pi*alpha*(M+(j:ℝ))+theta)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by
  by_cases ha : 0 ≤ a
  · have hcast : (a.natAbs:ℝ) = (a:ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℝ)) (Int.natAbs_of_nonneg ha)
    exact quadratic_rational_block_nat a.natAbs q N hq haq hN alpha beta theta M A C
      (by simpa [hcast] using halpha) hbeta hA hC
  · have hcast : (a.natAbs:ℝ) = -(a:ℝ) := by
      simpa only [Int.cast_natCast,Int.cast_neg,Int.natAbs_neg] using congrArg (fun z:ℤ => (z:ℝ))
        (Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_not_ge ha)))
    have halpha' : -alpha = (a.natAbs:ℝ)/(q:ℝ)+(-beta) := by rw [hcast,halpha]; ring
    have hh := quadratic_rational_block_nat a.natAbs q N hq haq hN (-alpha) (-beta) (-theta) M A C
      halpha' (by simpa using hbeta) hA hC
    have hphase : ∀ j : ℕ, Real.pi*(-alpha)*(M+(j:ℝ))+(-theta) =
        -(Real.pi*alpha*(M+(j:ℝ))+theta) := by intro j; ring
    simpa only [hphase,safeCappedSquare_neg] using hh

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

/- The telescoping block partition follows the elementary construction also used
in Prove2Me submission 968ef56d-d4b0-42b8-99aa-5a18c7253fab (marwahaha,
with Apache 2.0 attribution to Gershon Bialer). -/
theorem sum_consecutive_blocks {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (c : ℕ → ℕ) (hc : Monotone c) (hc0 : c 0 = 0) (J : ℕ) :
    (∑ d ∈ Ico 0 (c J), f d) = ∑ j ∈ range J, ∑ d ∈ Ico (c j) (c (j+1)), f d := by
  induction J with
  | zero => simp [hc0]
  | succ J ih =>
    rw [sum_range_succ,← ih]
    have h0 : 0 ≤ c J := Nat.zero_le _
    exact (sum_Ico_consecutive f h0 (hc (Nat.le_succ J))).symm

theorem sum_range_partition_blocks {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) (L q : ℕ) (hq : 0 < q) :
    (∑ j ∈ range L, f j) =
      ∑ k ∈ range (L/q+1), ∑ j ∈ range (min q (L-k*q)), f (k*q+j) := by
  let c : ℕ → ℕ := fun k => min L (k*q)
  have hc : Monotone c := fun i j hij => min_le_min_left _ (Nat.mul_le_mul_right _ hij)
  have hc0 : c 0 = 0 := by simp [c]
  have hcut : c (L/q+1) = L := by
    apply min_eq_left
    have hh := Nat.mod_lt L hq
    have hmod := Nat.div_add_mod L q
    rw [Nat.add_mul,Nat.one_mul]
    nlinarith
  have hh := sum_consecutive_blocks f c hc hc0 (L/q+1)
  rw [hcut,Nat.Ico_zero_eq_range] at hh
  rw [hh]
  apply sum_congr rfl
  intro k hk
  have hkq : k*q ≤ L := by
    have hkdiv : k ≤ L/q := by have := mem_range.mp hk; omega
    exact (Nat.mul_le_mul_right q hkdiv).trans (Nat.div_mul_le_self L q)
  have hck : c k = k*q := min_eq_right hkq
  have hlen : c (k+1)-c k = min q (L-k*q) := by
    dsimp [c]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  rw [sum_Ico_eq_sum_range,hlen,hck]

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem quadratic_rational_long_int (a : ℤ) (q N : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (theta beta phi M A C : ℝ)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2)
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ range N, safeCappedSquare A C (Real.pi*theta*(M+(j:ℝ))+phi)) ≤
      ((N/q+1:ℕ):ℝ)*(2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C))) := by
  rw [sum_range_partition_blocks _ N q (by omega)]
  calc
    _ ≤ ∑ k ∈ range (N/q+1), (2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C))) := by
      apply sum_le_sum
      intro k hk
      have hh := quadratic_rational_block_int a q (min q (N-k*q)) hq haq (min_le_left _ _)
        theta beta phi (M+(k*q:ℕ)) A C htheta hbeta hA hC
      simpa only [Nat.cast_add,add_assoc] using hh
    _ = _ := by simp; ring

theorem quadratic_rational_interval_row (a : ℤ) (q C D : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (theta beta m A B : ℝ)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑ n ∈ Ico C D, safeCappedSquare A B (Real.pi*((n:ℝ)-m)*theta)) ≤
      (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B))) := by
  rw [sum_Ico_eq_sum_range]
  have hh := quadratic_rational_long_int a q (D-C) hq haq theta beta 0 ((C:ℝ)-m) A B
    htheta hbeta hA hB
  convert hh using 1
  apply sum_congr rfl
  intro j hj
  congr 1
  push_cast
  ring

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem one_jump_variation_partial (g : ℕ → ℝ) (k : ℕ)
    (hg0 : ∀ n, 0 ≤ g n) (hzero : ∀ n < k, g n = 0)
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) (N : ℕ) :
    g 0+(∑ n ∈ range N, |g (n+1)-g n|) =
      if N ≤ k then g N else g k+|g (k+1)-g k|+g (k+1)-g N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,← add_assoc,ih]
    by_cases hNk : N < k
    · have hN : N ≤ k := by omega
      have hN1 : N+1 ≤ k := by omega
      simp only [if_pos hN,if_pos hN1,hzero N hNk,sub_zero,abs_of_nonneg (hg0 _),zero_add]
    · by_cases hNe : N = k
      · subst N
        simp only [le_refl,if_true,show ¬k+1 ≤ k by omega,if_false]
        ring
      · have hN : ¬N ≤ k := by omega
        have hN1 : ¬N+1 ≤ k := by omega
        rw [if_neg hN,if_neg hN1,abs_of_nonpos (sub_nonpos.mpr (hanti N (by omega)))]
        ring

theorem one_jump_variation (g : ℕ → ℝ) (k : ℕ) (B : ℝ)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ B) (hzero : ∀ n < k, g n = 0)
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) :
    Summable (fun n => |g (n+1)-g n|) ∧
      g 0+(∑' n : ℕ, |g (n+1)-g n|) ≤ 2*B := by
  have hpartial : ∀ N, (∑ n ∈ range N, |g (n+1)-g n|) ≤ 2*B-g 0 := by
    intro N
    have hh := one_jump_variation_partial g k (fun n => (hg n).1) hzero hanti N
    by_cases hN : N ≤ k
    · rw [if_pos hN] at hh
      have hB : 0 ≤ B := (hg 0).1.trans (hg 0).2
      linarith [(hg N).2]
    · rw [if_neg hN] at hh
      have habs : |g (k+1)-g k| ≤ 2*B-g k-g (k+1) := by
        apply abs_le.mpr
        constructor <;> linarith [(hg k).2,(hg (k+1)).2]
      linarith [(hg N).1]
  refine ⟨summable_of_sum_range_le (fun n => abs_nonneg _) hpartial,?_⟩
  have hh := Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hpartial
  linarith

noncomputable def clippedLog (c t : ℝ) : ℝ := Real.log (max t c)
noncomputable def clippedLogStep (c : ℝ) (n : ℕ) : ℝ :=
  clippedLog c ((n:ℝ)+1)-clippedLog c (n:ℝ)

theorem clippedLogStep_bounds (c : ℝ) (hc : 0 < c) (n : ℕ) :
    0 ≤ clippedLogStep c n ∧ clippedLogStep c n ≤ 1/c := by
  have hlo : 0 < max (n:ℝ) c := hc.trans_le (le_max_right _ _)
  have hhi : 0 < max ((n:ℝ)+1) c := hc.trans_le (le_max_right _ _)
  have hmono : max (n:ℝ) c ≤ max ((n:ℝ)+1) c := max_le_max_right _ (by linarith)
  have hdiff : max ((n:ℝ)+1) c-max (n:ℝ) c ≤ 1 := by
    calc
      _ ≤ max (((n:ℝ)+1)-(n:ℝ)) (c-c) := max_sub_max_le_max _ _ _ _
      _ = 1 := by norm_num
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hlo hmono)
  · have hh := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
    rw [Real.log_div (ne_of_gt hhi) (ne_of_gt hlo)] at hh
    change Real.log (max ((n:ℝ)+1) c)-Real.log (max (n:ℝ) c) ≤ _
    calc
      _ ≤ max ((n:ℝ)+1) c/max (n:ℝ) c-1 := hh
      _ = (max ((n:ℝ)+1) c-max (n:ℝ) c)/max (n:ℝ) c := by field_simp
      _ ≤ 1/max (n:ℝ) c := div_le_div_of_nonneg_right hdiff hlo.le
      _ ≤ 1/c := one_div_le_one_div_of_le hc (le_max_right _ _)

theorem clippedLogStep_zero (c : ℝ) (n : ℕ) (hn : n < ⌊c⌋₊) :
    clippedLogStep c n = 0 := by
  have hnf : n+1 ≤ ⌊c⌋₊ := by omega
  have hc : 0 ≤ c := by
    by_contra hc
    have hf : ⌊c⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  have hnc : (n:ℝ)+1 ≤ c := by
    have hh : ((n+1:ℕ):ℝ) ≤ (⌊c⌋₊:ℝ) := by exact_mod_cast hnf
    push_cast at hh
    exact hh.trans (Nat.floor_le hc)
  simp [clippedLogStep,clippedLog,max_eq_right hnc,max_eq_right (show (n:ℝ) ≤ c by linarith)]

theorem clippedLogStep_antitone_tail (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : ⌊c⌋₊+1 ≤ n) : clippedLogStep c (n+1) ≤ clippedLogStep c n := by
  have hnc : c < (n:ℝ) := by
    have hh : (⌊c⌋₊:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hn
    exact (Nat.lt_floor_add_one c).trans_le hh
  have hn0 : (0:ℝ) < n := hc.trans hnc
  have hn1 : c ≤ (n:ℝ)+1 := by linarith
  have hn2 : c ≤ (n:ℝ)+1+1 := by linarith
  simp only [clippedLogStep,clippedLog,Nat.cast_add,Nat.cast_one,
    max_eq_left hnc.le,max_eq_left hn1,max_eq_left hn2]
  rw [← Real.log_div (by positivity : (n:ℝ)+1+1 ≠ 0) (by positivity : (n:ℝ)+1 ≠ 0),
    ← Real.log_div (by positivity : (n:ℝ)+1 ≠ 0) (ne_of_gt hn0)]
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ (by positivity) hn0).mpr
  nlinarith

theorem clippedLogStep_variation (c : ℝ) (hc : 0 < c) :
    Summable (fun n => |clippedLogStep c (n+1)-clippedLogStep c n|) ∧
      clippedLogStep c 0+(∑' n : ℕ, |clippedLogStep c (n+1)-clippedLogStep c n|) ≤ 2/c := by
  have hh := one_jump_variation (clippedLogStep c) ⌊c⌋₊ (1/c)
    (clippedLogStep_bounds c hc) (clippedLogStep_zero c) (clippedLogStep_antitone_tail c hc)
  simpa [div_eq_mul_inv] using hh

theorem clippedLog_second_variation (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℤ => |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|) ∧
      (∑' n : ℤ, |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|) ≤ 2/c := by
  let f : ℤ → ℝ := fun n => |clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n|
  have hnat : ∀ n : ℕ, f n = |clippedLogStep c (n+1)-clippedLogStep c n| := by
    intro n
    dsimp [f,clippedLogStep]
    push_cast
    congr 1
    rw [show (n:ℝ)+1+1 = (n:ℝ)+2 by ring]
    ring
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = if n = 0 then clippedLogStep c 0 else 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hc0 : max (0:ℝ) c = c := max_eq_right hc.le
      have hc1 : max (-1:ℝ) c = c := max_eq_right (by linarith)
      simp only [f,Nat.cast_zero,zero_add,Int.cast_neg,Int.cast_one,neg_add_cancel,
        show (-1:ℝ)+2 = 1 by norm_num,clippedLog,hc0,hc1,if_pos rfl,
        clippedLogStep,Nat.cast_zero,zero_add]
      rw [show Real.log (max 1 c)-2*Real.log c+Real.log c = Real.log (max 1 c)-Real.log c by ring]
      apply abs_of_nonneg
      simpa [clippedLogStep,clippedLog,hc0] using (clippedLogStep_bounds c hc 0).1
    · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have h0 : -(n:ℝ)-1 ≤ c := by linarith
      have h1 : -(n:ℝ)-1+1 ≤ c := by linarith
      have h2 : -(n:ℝ)-1+2 ≤ c := by linarith
      dsimp [f]
      push_cast
      rw [show -((n:ℝ)+1) = -(n:ℝ)-1 by ring]
      simp only [clippedLog,max_eq_right h0,max_eq_right h1,max_eq_right h2,if_neg hn]
      rw [show Real.log c-2*Real.log c+Real.log c = 0 by ring]
      exact abs_zero
  have hv := clippedLogStep_variation c hc
  have hsNat : Summable (fun n : ℕ => f n) := by simpa only [hnat] using hv.1
  have hsNeg : Summable (fun n : ℕ => f (-((n:ℤ)+1))) := by
    simp_rw [hneg]
    exact (hasSum_ite_eq (0:ℕ) (clippedLogStep c 0)).summable
  refine ⟨hsNat.of_nat_of_neg_add_one hsNeg,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  rw [tsum_of_nat_of_neg_add_one hsNat hsNeg]
  simp_rw [hnat,hneg]
  simpa [add_comm] using hv.2

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem clippedLog_eq_max_log (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    clippedLog c t = max (Real.log t) (Real.log c) := by
  by_cases htc : t ≤ c
  · simp [clippedLog,max_eq_right htc,max_eq_right (Real.log_le_log ht htc)]
  · have hct := (le_of_not_ge htc)
    simp [clippedLog,max_eq_left hct,max_eq_left (Real.log_le_log hc hct)]

theorem log_tent_identity (L Y b : ℝ) (hb : 0 ≤ b) :
    max (b-|b+L-Y|) 0 = max L (Y-2*b)-2*max L (Y-b)+max L Y := by
  by_cases h0 : L ≤ Y-2*b
  · have h1 : L ≤ Y-b := by linarith
    have h2 : L ≤ Y := by linarith
    rw [max_eq_right h0,max_eq_right h1,max_eq_right h2,
      abs_of_nonpos (show b+L-Y ≤ 0 by linarith),max_eq_right (by linarith)]
    ring
  · by_cases h1 : L ≤ Y-b
    · have h2 : L ≤ Y := by linarith
      rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_right h1,max_eq_right h2,
        abs_of_nonpos (show b+L-Y ≤ 0 by linarith),max_eq_left (by linarith)]
      ring
    · by_cases h2 : L ≤ Y
      · rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_left (by linarith : Y-b ≤ L),
          max_eq_right h2,abs_of_nonneg (show 0 ≤ b+L-Y by linarith),max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith : Y-2*b ≤ L),max_eq_left (by linarith : Y-b ≤ L),
          max_eq_left (by linarith : Y ≤ L),abs_of_nonneg (show 0 ≤ b+L-Y by linarith),
          max_eq_right (by linarith)]
        ring

theorem etaTwo_clippedLog (y t : ℝ) (hy : 0 < y) :
    Helfgott.etaTwo (t/y) =
      4*(clippedLog (y/4) t-2*clippedLog (y/2) t+clippedLog y t) := by
  have hy2 : 0 < y/2 := by positivity
  have hy4 : 0 < y/4 := by positivity
  have hl2 : Real.log (y/2) = Real.log y-Real.log 2 := Real.log_div (ne_of_gt hy) (by norm_num)
  have hl4 : Real.log (y/4) = Real.log y-2*Real.log 2 := by
    rw [Real.log_div (ne_of_gt hy) (by norm_num),show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  by_cases ht : 0 < t
  · rw [Helfgott.etaTwo,if_pos (div_pos ht hy),clippedLog_eq_max_log _ _ hy4 ht,
      clippedLog_eq_max_log _ _ hy2 ht,clippedLog_eq_max_log _ _ hy ht,hl2,hl4]
    have hlog : Real.log (2*(t/y)) = Real.log 2+Real.log t-Real.log y := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (div_pos ht hy)),Real.log_div (ne_of_gt ht) (ne_of_gt hy)]
      ring
    rw [hlog,log_tent_identity (Real.log t) (Real.log y) (Real.log 2) (Real.log_nonneg (by norm_num))]
  · have ht0 : t ≤ 0 := le_of_not_gt ht
    rw [Helfgott.etaTwo,if_neg (not_lt.mpr (div_nonpos_of_nonpos_of_nonneg ht0 hy.le))]
    simp only [clippedLog,max_eq_right (ht0.trans hy4.le),max_eq_right (ht0.trans hy2.le),
      max_eq_right (ht0.trans hy.le),hl2,hl4]
    ring

theorem etaTwo_second_variation (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|) ∧
    (∑' n : ℤ, |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|) ≤ 72/y := by
  let d : ℝ → ℤ → ℝ := fun c n => clippedLog c ((n:ℝ)+2)-2*clippedLog c ((n:ℝ)+1)+clippedLog c n
  let f : ℤ → ℝ := fun n => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|
  have hpoint : ∀ n, f n ≤ 4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n| := by
    intro n
    have heq : f n = |4*d (y/4) n-8*d (y/2) n+4*d y n| := by
      dsimp [f,d]
      simp_rw [etaTwo_clippedLog y _ hy]
      congr 1
      ring
    rw [heq]
    calc
      _ ≤ |4*d (y/4) n-8*d (y/2) n|+|4*d y n| := abs_add_le _ _
      _ ≤ (|4*d (y/4) n|+|8*d (y/2) n|)+|4*d y n| := add_le_add (abs_sub _ _) le_rfl
      _ = _ := by simp [abs_mul]
  have h4 := clippedLog_second_variation (y/4) (by positivity)
  have h2 := clippedLog_second_variation (y/2) (by positivity)
  have h1 := clippedLog_second_variation y hy
  have hmajor : Summable (fun n : ℤ => 4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n|) :=
    ((h4.1.mul_left 4).add (h2.1.mul_left 8)).add (h1.1.mul_left 4)
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  calc
    _ ≤ (∑' n : ℤ, (4*|d (y/4) n|+8*|d (y/2) n|+4*|d y n|)) := hf.tsum_le_tsum hpoint hmajor
    _ = 4*(∑' n : ℤ, |d (y/4) n|)+8*(∑' n : ℤ, |d (y/2) n|)+4*(∑' n : ℤ, |d y n|) := by
      rw [Summable.tsum_add ((h4.1.mul_left 4).add (h2.1.mul_left 8)) (h1.1.mul_left 4),
        Summable.tsum_add (h4.1.mul_left 4) (h2.1.mul_left 8)]
      simp only [tsum_mul_left,d]
    _ ≤ 4*(2/(y/4))+8*(2/(y/2))+4*(2/y) := by
      have hh4 := h4.2
      have hh2 := h2.2
      have hh1 := h1.2
      change (∑' n : ℤ, |d (y/4) n|) ≤ _ at hh4
      change (∑' n : ℤ, |d (y/2) n|) ≤ _ at hh2
      change (∑' n : ℤ, |d y n|) ≤ _ at hh1
      linarith
    _ = 72/y := by ring

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem summable_twisted (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) : Summable (fun n => a n*z^n) := by
  apply ha.of_norm_bounded
  intro n
  simp [norm_mul,norm_zpow,hz]

theorem summable_backward (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    Summable (fun n => ‖a (n-1)-a n‖) := by
  have hshift : Summable (fun n : ℤ => ‖a (n-1)‖) :=
    ((Equiv.subRight (1:ℤ)).summable_iff).mpr ha
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_sub_le _ _) (hshift.add ha)

theorem backward_twisted_identity (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' n : ℤ, (a (n-1)-a n)*z^n) = (z-1)*(∑' n : ℤ, a n*z^n) := by
  have hz0 : z ≠ 0 := by intro hh; simp [hh] at hz
  have hshift : Summable (fun n : ℤ => ‖a (n-1)‖) :=
    ((Equiv.subRight (1:ℤ)).summable_iff).mpr ha
  have hs1 := summable_twisted (fun n => a (n-1)) hshift z hz
  have hs0 := summable_twisted a ha z hz
  have heq : (∑' n : ℤ, a (n-1)*z^n) = z*(∑' n : ℤ, a n*z^n) := by
    rw [← (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => a (n-1)*z^n)]
    simp only [Equiv.coe_addRight,add_sub_cancel_right,zpow_add₀ hz0,zpow_one]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  simp_rw [sub_mul]
  rw [hs1.tsum_sub hs0,heq]
  ring

theorem second_difference_twisted_identity (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    (∑' n : ℤ, (a (n-2)-2*a (n-1)+a n)*z^n) = (z-1)^2*(∑' n : ℤ, a n*z^n) := by
  have hh := backward_twisted_identity (fun n => a (n-1)-a n) (summable_backward a ha) z hz
  rw [backward_twisted_identity a ha z hz] at hh
  have heq : ∀ n : ℤ, (a (n-1-1)-a (n-1))-(a (n-1)-a n) = a (n-2)-2*a (n-1)+a n := by
    intro n
    rw [show n-1-1 = n-2 by omega]
    ring
  simpa only [heq,pow_two,mul_assoc] using hh

theorem second_difference_twisted_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z-1‖^2*‖∑' n : ℤ, a n*z^n‖ ≤ ∑' n : ℤ, ‖a (n-2)-2*a (n-1)+a n‖ := by
  have hdiff : Summable (fun n : ℤ => ‖a (n-2)-2*a (n-1)+a n‖) := by
    have hh := summable_backward (fun n => a (n-1)-a n) (summable_backward a ha)
    convert hh using 1
    ext n
    congr 1
    rw [show n-1-1 = n-2 by omega]
    ring
  have htwist : Summable (fun n : ℤ => ‖(a (n-2)-2*a (n-1)+a n)*z^n‖) := by
    simpa only [norm_mul,norm_zpow,hz,one_zpow,mul_one] using hdiff
  have hh := norm_tsum_le_tsum_norm htwist
  rw [second_difference_twisted_identity a ha z hz] at hh
  simpa only [norm_mul,norm_pow,norm_zpow,hz,one_zpow,mul_one] using hh

theorem second_difference_exponential_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖)) (theta : ℝ) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖∑' n : ℤ, a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ ≤
        ∑' n : ℤ, ‖a (n-2)-2*a (n-1)+a n‖ := by
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hnorm : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))-1‖^2 =
      4*(Real.sin (Real.pi*theta))^2 := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2*Real.pi*theta/2 = Real.pi*theta by ring]
    simp only [Real.norm_eq_abs,sq_abs]
    ring
  have hh := second_difference_twisted_bound a ha _ hz
  rwa [hnorm] at hh

end HelfgottQuadratic

end

section

open Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_zero_nonpos (t : ℝ) (ht : t ≤ 0) : Helfgott.etaTwo t = 0 := by
  simp [Helfgott.etaTwo,not_lt.mpr ht]

theorem etaTwo_zero_large (y t : ℝ) (hy : 0 < y) (ht : y ≤ t) :
    Helfgott.etaTwo (t/y) = 0 := by
  rw [etaTwo_clippedLog y t hy]
  have ht2 : y/2 ≤ t := by linarith
  have ht4 : y/4 ≤ t := by linarith
  simp only [clippedLog,max_eq_left ht,max_eq_left ht2,max_eq_left ht4]
  ring

theorem etaTwo_nonneg (t : ℝ) : 0 ≤ Helfgott.etaTwo t := by
  unfold Helfgott.etaTwo
  split_ifs
  · positivity
  · rfl

theorem etaTwo_le_log_two (t : ℝ) : Helfgott.etaTwo t ≤ 4*Real.log 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold Helfgott.etaTwo
  split_ifs
  · exact mul_le_mul_of_nonneg_left (max_le (sub_le_self _ (abs_nonneg _)) hl) (by norm_num)
  · positivity

theorem etaTwo_int_support (y : ℝ) (hy : 0 < y) (n : ℤ)
    (hn : n ∉ Icc (1:ℤ) ⌊y⌋) : Helfgott.etaTwo ((n:ℝ)/y) = 0 := by
  by_cases hn0 : n < 1
  · apply etaTwo_zero_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (show n ≤ 0 by omega)) hy.le
  · have hnf : ⌊y⌋ < n := by simp only [mem_Icc,not_and_or,not_le] at hn; omega
    have hny : y ≤ (n:ℝ) := by
      have hh : (⌊y⌋:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hnf
      exact (Int.lt_floor_add_one y).le.trans hh
    exact etaTwo_zero_large y n hy hny

theorem etaTwo_int_summable (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) := by
  apply summable_of_ne_finset_zero (s := Icc (1:ℤ) ⌊y⌋)
  intro n hn
  simp [etaTwo_int_support y hy n hn]

theorem etaTwo_int_energy (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) ≤ (4*Real.log 2)*(⌊y⌋₊:ℝ) := by
  rw [tsum_eq_sum (s := Icc (1:ℤ) ⌊y⌋) (fun n hn => by simp [etaTwo_int_support y hy n hn])]
  calc
    _ ≤ ∑ _n ∈ Icc (1:ℤ) ⌊y⌋, 4*Real.log 2 := by
      apply sum_le_sum
      intro n hn
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (etaTwo_nonneg _)] using etaTwo_le_log_two ((n:ℝ)/y)
    _ = (4*Real.log 2)*(⌊y⌋₊:ℝ) := by simp [Int.card_Icc,Int.floor_toNat,mul_comm]

theorem etaTwo_int_second_bound (y : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ‖((Helfgott.etaTwo (((n-2:ℤ):ℝ)/y)):ℂ)-
        2*((Helfgott.etaTwo (((n-1:ℤ):ℝ)/y)):ℂ)+((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖) ≤ 72/y := by
  let f : ℤ → ℝ := fun n => |Helfgott.etaTwo (((n:ℝ)+2)/y)-
      2*Helfgott.etaTwo (((n:ℝ)+1)/y)+Helfgott.etaTwo ((n:ℝ)/y)|
  have heq : ∀ n : ℤ, ‖((Helfgott.etaTwo (((n-2:ℤ):ℝ)/y)):ℂ)-
        2*((Helfgott.etaTwo (((n-1:ℤ):ℝ)/y)):ℂ)+((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖ = f (n-2) := by
    intro n
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs]
    dsimp [f]
    push_cast
    rw [show (n:ℝ)-2+2 = (n:ℝ) by ring,show (n:ℝ)-2+1 = (n:ℝ)-1 by ring]
    congr 1
    ring
  simp_rw [heq]
  have hh := (Equiv.subRight (2:ℤ)).tsum_eq f
  change (∑' n : ℤ, f (n-2)) = (∑' n : ℤ, f n) at hh
  rw [hh]
  exact (etaTwo_second_variation y hy).2

theorem etaTwo_int_sum_eq_expSum (y theta : ℝ) (hy : 0 < y) :
    (∑' n : ℤ, ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n) =
        Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ)) := by
  let z := Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))
  let f : ℤ → ℂ := fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*z^n
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hs : Summable f := summable_twisted _ (etaTwo_int_summable y hy) z hz
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    have hn : ((-((n:ℤ)+1):ℤ):ℝ)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    simp only [f,etaTwo_zero_nonpos _ hn,Complex.ofReal_zero,zero_mul]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one (hs.comp_injective Nat.cast_injective)
    (hs.comp_injective (by
      intro n m h
      apply Nat.cast_injective (R:=ℤ)
      linarith : Function.Injective (fun n:ℕ => -((n:ℤ)+1))))]
  simp_rw [hneg]
  rw [tsum_zero,add_zero]
  unfold Helfgott.expSum
  apply tsum_congr
  intro n
  change ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*z^(n:ℤ) =
    ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  apply congrArg (fun w : ℂ => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*w)
  change (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^(n:ℤ) =
    fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  rw [fourier_coe_apply,← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem etaTwo_expSum_quadratic (y theta : ℝ) (hy : 0 < y) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤ 72/y := by
  have hh := second_difference_exponential_bound _ (etaTwo_int_summable y hy) theta
  rw [etaTwo_int_sum_eq_expSum y theta hy] at hh
  exact hh.trans (etaTwo_int_second_bound y hy)

theorem etaTwo_expSum_trivial (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log 2)*(⌊y⌋₊:ℝ) := by
  rw [← etaTwo_int_sum_eq_expSum y theta hy]
  have hs := etaTwo_int_summable y hy
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have hnorm : ∀ n : ℤ, ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ = ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)‖ := by
    intro n
    simp only [norm_mul,norm_zpow,hz,one_zpow,mul_one]
  have hh := norm_tsum_le_tsum_norm (show Summable (fun n : ℤ => ‖((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖) by simpa only [hnorm] using hs)
  simp_rw [hnorm] at hh
  exact hh.trans (etaTwo_int_energy y hy)

theorem etaTwo_expSum_quadratic_cap (y theta : ℝ) (hy : 0 < y) :
    ‖Helfgott.expSum (fun n => ((Helfgott.etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      if Real.sin (Real.pi*theta) = 0 then (4*Real.log 2)*(⌊y⌋₊:ℝ)
      else min ((4*Real.log 2)*(⌊y⌋₊:ℝ)) (18/(y*(Real.sin (Real.pi*theta))^2)) := by
  by_cases hsin : Real.sin (Real.pi*theta) = 0
  · rw [if_pos hsin]
    exact etaTwo_expSum_trivial y theta hy
  · rw [if_neg hsin]
    refine le_min (etaTwo_expSum_trivial y theta hy) ?_
    apply (le_div_iff₀ (mul_pos hy (sq_pos_of_ne_zero hsin))).mpr
    have hh := (le_div_iff₀ hy).mp (etaTwo_expSum_quadratic y theta hy)
    nlinarith

end HelfgottQuadratic

end

section
/- Arithmetic and finite-convolution infrastructure retained from accepted
Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai,
published October 6, 2026. Apache 2.0. The analytic cancellation proof is omitted;
the new quadratic estimate is supplied separately. -/

open Finset
open scoped BigOperators
namespace Helfgott

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]


lemma etaTwo_arithmetic_eq_zero (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 (Nat.floor y)) : f n*etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : Nat.floor y < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have hh := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_arithmetic_summable (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 (Nat.floor y))
  intro n hn
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

lemma etaTwo_arithmetic_expSum_finite (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor y), ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  dsimp only
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp


theorem truncated_divisor_sum_complex (B : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

lemma etaTwo_convolution_expSum_hyperbola (f g : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => (((f*g) n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (Nat.floor y), ∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
        ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have hindex : Finset.Ioc 0 (Nat.floor y) = Finset.Icc 1 (Nat.floor y) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  let F (d m : ℕ) : ℂ :=
    ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α
  rw [etaTwo_arithmetic_expSum_finite _ y hy α,hindex]
  have hinner (k : ℕ) :
      (((f*g) k*etaTwo ((k : ℝ)/y) : ℝ) : ℂ)*fourier (k : ℤ) α =
      ∑ d ∈ k.divisors, F d (k/d) := by
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)]
    rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have he : d*(k/d) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    simp only [F,he,Complex.ofReal_mul]
  simp_rw [hinner]
  rw [truncated_divisor_sum_complex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]


lemma sum_Icc_of_high_zero (F : ℕ → ℂ) (U B : ℕ) (hF : ∀ n, U < n → F n = 0) :
    (∑ n ∈ Finset.Icc 1 B, F n) = ∑ n ∈ Finset.Icc 1 (min U B), F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨h1,h2.trans (min_le_right _ _)⟩
  · intro n hn hnot
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    have hnU : U < n := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨h1,le_min (le_of_not_gt h) h2⟩)
    exact hF n hnU


lemma arithmeticCutoff_convolution_zero_above (U V n : ℕ) (f g : ArithmeticFunction ℝ)
    (hn : U*V < n) : (arithmeticCutoff U f*arithmeticCutoff V g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod : p.1*p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hU : p.1 ≤ U
  · have hV : ¬p.2 ≤ V := by
      intro h
      have hh := Nat.mul_le_mul hU h
      rw [hprod] at hh
      omega
    simp [arithmeticCutoff,hV]
  · simp [arithmeticCutoff,hU]

lemma vaughan_correction_expSum (U V : ℕ) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (min (U*V) (Nat.floor y)),
        (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
          arithmeticCutoff V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ)*
        (∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
          ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α) := by
  rw [vaughanCorrection,etaTwo_convolution_expSum_hyperbola _ _ y hy α]
  rw [sum_Icc_of_high_zero (U := U*V)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1;omega
    simp only [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hm0,Nat.cast_one,mul_one,
      Complex.ofReal_mul,mul_assoc]
  · intro d hd
    rw [arithmeticCutoff_convolution_zero_above U V d _ _ hd]
    simp


lemma fourier_product_frequency (d m : ℕ) (α : AddCircle (1 : ℝ)) :
    fourier ((d*m : ℕ) : ℤ) α = fourier (m : ℤ) ((d : ℤ) • α) := by
  simp only [fourier_apply,Nat.cast_mul,smul_smul,mul_comm]

lemma etaTwo_product_scale (d m : ℕ) (hd : 0 < d) (y : ℝ) (hy : 0 < y) :
    etaTwo (((d*m : ℕ) : ℝ)/y) = etaTwo ((m : ℝ)/(y/(d : ℝ))) := by
  congr 1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp


lemma arithmeticCutoff_moebius_abs_le (U n : ℕ) :
    |arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
  change |if n ≤ U then ((ArithmeticFunction.moebius n : ℤ) : ℝ) else 0| ≤ 1
  by_cases hn : n ≤ U
  · rw [if_pos hn]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · simp [hn]

lemma arithmeticCutoff_vonMangoldt_bounds (V n : ℕ) :
    0 ≤ arithmeticCutoff V ArithmeticFunction.vonMangoldt n ∧
      arithmeticCutoff V ArithmeticFunction.vonMangoldt n ≤ ArithmeticFunction.vonMangoldt n := by
  change (0 ≤ if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) ∧
    (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) ≤ ArithmeticFunction.vonMangoldt n
  by_cases hn : n ≤ V
  · simp only [if_pos hn]
    exact ⟨ArithmeticFunction.vonMangoldt_nonneg,le_rfl⟩
  · simp only [if_neg hn]
    exact ⟨le_rfl,ArithmeticFunction.vonMangoldt_nonneg⟩

lemma vaughan_correction_coefficient_abs_le (U V d : ℕ) :
    |(arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticCutoff V ArithmeticFunction.vonMangoldt) d| ≤ Real.log (d : ℝ) := by
  have he : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ)*ArithmeticFunction.vonMangoldt) d =
      Real.log (d : ℝ) := by
    rw [mul_comm,ArithmeticFunction.vonMangoldt_mul_zeta,ArithmeticFunction.log_apply]
  rw [← he,ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hd : d ≠ 0 := (Nat.mem_divisorsAntidiagonal.mp hp).2
  have hprod : p.1*p.2 = d := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hp1 : p.1 ≠ 0 := by intro h;rw [h,zero_mul] at hprod;exact hd hprod.symm
  rw [ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply_ne hp1,Nat.cast_one,one_mul,
    abs_mul,abs_of_nonneg (arithmeticCutoff_vonMangoldt_bounds V p.2).1]
  calc
    _ ≤ 1*arithmeticCutoff V ArithmeticFunction.vonMangoldt p.2 :=
      mul_le_mul_of_nonneg_right (arithmeticCutoff_moebius_abs_le U p.1)
        (arithmeticCutoff_vonMangoldt_bounds V p.2).1
    _ ≤ _ := by simpa only [one_mul] using (arithmeticCutoff_vonMangoldt_bounds V p.2).2


end Helfgott

end

section
/- Piecewise etaTwo formulas and monotonicity below are retained from accepted
Prove2Me submission 63b25d14-2999-434f-b84f-5af50fbd02fa by raresbuhai,
Apache 2.0, with the local namespace changed. The discrete variation proof
will be added separately. -/

open Helfgott Finset
open scoped BigOperators
namespace HelfgottQuadratic

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring


lemma etaTwo_monotone_lower (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1/2) :
    etaTwo s ≤ etaTwo t := by
  by_cases hs : 0 < s
  · have ht0 : 0 < t := hs.trans_le hst
    have hls : Real.log (2*s) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlt : Real.log (2*t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
    have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
    simp only [etaTwo,if_pos hs,if_pos ht0,abs_of_nonpos hls,abs_of_nonpos hlt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply max_le_max_right
    linarith
  · simpa [etaTwo,hs] using etaTwo_nonneg t

lemma etaTwo_antitone_upper (s t : ℝ) (hst : s ≤ t) (hs : 1/2 ≤ s) :
    etaTwo t ≤ etaTwo s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := hs0.trans_le hst
  have hls : 0 ≤ Real.log (2*s) := Real.log_nonneg (by linarith)
  have hlt : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*s) ≤ Real.log (2*t) := Real.log_le_log (by positivity) (by linarith)
  simp only [etaTwo,if_pos hs0,if_pos ht0,abs_of_nonneg hls,abs_of_nonneg hlt]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply max_le_max_right
  linarith


theorem single_peak_variation_partial (g : ℕ → ℝ) (k : ℕ)
    (hmono : ∀ n, n < k → g n ≤ g (n+1))
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) (N : ℕ) :
    g 0+(∑ n ∈ range N, |g (n+1)-g n|) =
      if N ≤ k then g N else g k+|g (k+1)-g k|+g (k+1)-g N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,← add_assoc,ih]
    by_cases hNk : N < k
    · have hN : N ≤ k := by omega
      have hN1 : N+1 ≤ k := by omega
      rw [if_pos hN,if_pos hN1,abs_of_nonneg (sub_nonneg.mpr (hmono N hNk))]
      ring
    · by_cases hNe : N = k
      · subst N
        simp only [le_refl,if_true,show ¬k+1 ≤ k by omega,if_false]
        ring
      · have hN : ¬N ≤ k := by omega
        have hN1 : ¬N+1 ≤ k := by omega
        rw [if_neg hN,if_neg hN1,abs_of_nonpos (sub_nonpos.mpr (hanti N (by omega)))]
        ring

theorem single_peak_variation (g : ℕ → ℝ) (k : ℕ) (B : ℝ)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ B) (hmono : ∀ n, n < k → g n ≤ g (n+1))
    (hanti : ∀ n, k+1 ≤ n → g (n+1) ≤ g n) :
    Summable (fun n => |g (n+1)-g n|) ∧
      g 0+(∑' n : ℕ, |g (n+1)-g n|) ≤ 2*B := by
  have hpartial : ∀ N, (∑ n ∈ range N, |g (n+1)-g n|) ≤ 2*B-g 0 := by
    intro N
    have hh := single_peak_variation_partial g k hmono hanti N
    by_cases hN : N ≤ k
    · rw [if_pos hN] at hh
      have hB : 0 ≤ B := (hg 0).1.trans (hg 0).2
      linarith [(hg N).2]
    · rw [if_neg hN] at hh
      have habs : |g (k+1)-g k| ≤ 2*B-g k-g (k+1) := by
        apply abs_le.mpr
        constructor <;> linarith [(hg k).2,(hg (k+1)).2]
      linarith [(hg N).1]
  refine ⟨summable_of_sum_range_le (fun n => abs_nonneg _) hpartial,?_⟩
  have hh := Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _) hpartial
  linarith

theorem etaTwo_first_variation_nat (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ∧
      (∑' n : ℕ, |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ≤ 8*Real.log 2 := by
  let g : ℕ → ℝ := fun n => etaTwo ((n:ℝ)/y)
  have hmono : ∀ n, n < ⌊y/2⌋₊ → g n ≤ g (n+1) := by
    intro n hn
    apply etaTwo_monotone_lower
    · apply div_le_div_of_nonneg_right _ hy.le
      push_cast
      linarith
    · apply (div_le_iff₀ hy).mpr
      have hnf : ((n+1:ℕ):ℝ) ≤ (⌊y/2⌋₊:ℝ) := by exact_mod_cast (show n+1 ≤ ⌊y/2⌋₊ by omega)
      have hfl := Nat.floor_le (show 0 ≤ y/2 by positivity)
      linarith
  have hanti : ∀ n, ⌊y/2⌋₊+1 ≤ n → g (n+1) ≤ g n := by
    intro n hn
    apply etaTwo_antitone_upper
    · apply div_le_div_of_nonneg_right _ hy.le
      push_cast
      linarith
    · apply (le_div_iff₀ hy).mpr
      have hnf : (⌊y/2⌋₊:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hn
      have hfl := Nat.lt_floor_add_one (y/2)
      linarith
  have hh := single_peak_variation g ⌊y/2⌋₊ (4*Real.log 2)
    (fun n => ⟨etaTwo_nonneg _,etaTwo_le_log_two _⟩) hmono hanti
  simpa only [g,Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_div,Helfgott.etaTwo,
    lt_self_iff_false,if_false,zero_add,show (2:ℝ)*(4*Real.log 2) = 8*Real.log 2 by ring] using hh

theorem etaTwo_first_variation (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ∧
      (∑' n : ℤ, |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|) ≤ 8*Real.log 2 := by
  let f : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|
  have hsNat : Summable (fun n : ℕ => f n) := by simpa only [f,Int.cast_natCast] using (etaTwo_first_variation_nat y hy).1
  have hneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    have h0 : ((-((n:ℤ)+1):ℤ):ℝ)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    have h1 : (((-((n:ℤ)+1):ℤ):ℝ)+1)/y ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hy.le
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    simp only [f,etaTwo_zero_nonpos _ h0,etaTwo_zero_nonpos _ h1,sub_self,abs_zero]
  have hsNeg : Summable (fun n : ℕ => f (-((n:ℤ)+1))) := by simp only [hneg]; exact summable_zero
  refine ⟨hsNat.of_nat_of_neg_add_one hsNeg,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  rw [tsum_of_nat_of_neg_add_one hsNat hsNeg]
  simp only [hneg,tsum_zero,add_zero]
  exact (etaTwo_first_variation_nat y hy).2

end HelfgottQuadratic

end

section

open Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

theorem clippedLog_increment_bounds (c t : ℝ) (hc : 0 < c) :
    0 ≤ clippedLog c (t+1)-clippedLog c t ∧
      clippedLog c (t+1)-clippedLog c t ≤ 1/c := by
  have hlo : 0 < max t c := hc.trans_le (le_max_right _ _)
  have hhi : 0 < max (t+1) c := hc.trans_le (le_max_right _ _)
  have hmono : max t c ≤ max (t+1) c := max_le_max_right _ (by linarith)
  have hdiff : max (t+1) c-max t c ≤ 1 := by
    calc
      _ ≤ max ((t+1)-t) (c-c) := max_sub_max_le_max _ _ _ _
      _ = 1 := by norm_num
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hlo hmono)
  · have hh := Real.log_le_sub_one_of_pos (div_pos hhi hlo)
    rw [Real.log_div (ne_of_gt hhi) (ne_of_gt hlo)] at hh
    change Real.log (max (t+1) c)-Real.log (max t c) ≤ _
    calc
      _ ≤ max (t+1) c/max t c-1 := hh
      _ = (max (t+1) c-max t c)/max t c := by field_simp
      _ ≤ 1/max t c := div_le_div_of_nonneg_right hdiff hlo.le
      _ ≤ 1/c := one_div_le_one_div_of_le hc (le_max_right _ _)

theorem etaTwo_log_clipped (y t : ℝ) (hy : 0 < y) :
    Real.log t*etaTwo (t/y) = clippedLog (y/8) t*etaTwo (t/y) := by
  by_cases ht : y/8 ≤ t
  · simp [clippedLog,max_eq_left ht]
  · have ht' : t/y < 1/4 := (div_lt_iff₀ hy).mpr (by linarith)
    have hz := etaTwo_eq_zero_of_not_mem (t/y) (fun hh => (not_le_of_gt ht') hh.1)
    rw [hz,mul_zero,mul_zero]

theorem clippedLog_endpoint_bound (y t : ℝ) (hy : 8 ≤ y) (ht : t ≤ y) :
    |clippedLog (y/8) (t+2)| ≤ Real.log (y+2) := by
  have hlo : (1:ℝ) ≤ max (t+2) (y/8) := le_trans (by linarith) (le_max_right _ _)
  have hhi : max (t+2) (y/8) ≤ y+2 := max_le (by linarith) (by linarith)
  rw [clippedLog,abs_of_nonneg (Real.log_nonneg hlo)]
  exact Real.log_le_log (by linarith) hhi

theorem etaTwo_log_second_pointwise (y t : ℝ) (hy : 8 ≤ y) :
    |Real.log (t+2)*etaTwo ((t+2)/y)-2*(Real.log (t+1)*etaTwo ((t+1)/y))+
        Real.log t*etaTwo (t/y)| ≤
      Real.log (y+2)*|etaTwo ((t+2)/y)-2*etaTwo ((t+1)/y)+etaTwo (t/y)| +
      (16/y)*|etaTwo ((t+1)/y)-etaTwo (t/y)| +
      (4*Real.log 2)*|clippedLog (y/8) (t+2)-2*clippedLog (y/8) (t+1)+clippedLog (y/8) t| := by
  have hyp : 0 < y := by linarith
  let a := clippedLog (y/8)
  let b : ℝ → ℝ := fun t => etaTwo (t/y)
  have heq : Real.log (t+2)*etaTwo ((t+2)/y)-2*(Real.log (t+1)*etaTwo ((t+1)/y))+
        Real.log t*etaTwo (t/y) =
      a (t+2)*(b (t+2)-2*b (t+1)+b t)+2*(a (t+2)-a (t+1))*(b (t+1)-b t)+
        (a (t+2)-2*a (t+1)+a t)*b t := by
    simp_rw [etaTwo_log_clipped y _ hyp]
    dsimp [a,b]
    ring
  have hfirst : |a (t+2)*(b (t+2)-2*b (t+1)+b t)| ≤
      Real.log (y+2)*|b (t+2)-2*b (t+1)+b t| := by
    by_cases ht : t ≤ y
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (clippedLog_endpoint_bound y t hy ht) (abs_nonneg _)
    · have hb0 : b t = 0 := etaTwo_zero_large y t hyp (le_of_not_ge ht)
      have hb1 : b (t+1) = 0 := etaTwo_zero_large y (t+1) hyp (by linarith)
      have hb2 : b (t+2) = 0 := etaTwo_zero_large y (t+2) hyp (by linarith)
      simp [hb0,hb1,hb2]
  have hinc : |a (t+2)-a (t+1)| ≤ 8/y := by
    have hh := clippedLog_increment_bounds (y/8) (t+1) (by positivity)
    rw [show t+1+1 = t+2 by ring] at hh
    rw [abs_of_nonneg hh.1]
    convert hh.2 using 1 <;> ring
  have hcross : |2*(a (t+2)-a (t+1))*(b (t+1)-b t)| ≤ (16/y)*|b (t+1)-b t| := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (2*(8/y))*|b (t+1)-b t| := by gcongr
      _ = _ := by ring
  have hlast : |(a (t+2)-2*a (t+1)+a t)*b t| ≤
      (4*Real.log 2)*|a (t+2)-2*a (t+1)+a t| := by
    rw [abs_mul,abs_of_nonneg (etaTwo_nonneg _)]
    calc
      _ ≤ |a (t+2)-2*a (t+1)+a t| * (4*Real.log 2) :=
        mul_le_mul_of_nonneg_left (etaTwo_le_log_two _) (abs_nonneg _)
      _ = _ := by ring
  rw [heq]
  calc
    _ ≤ |a (t+2)*(b (t+2)-2*b (t+1)+b t)+2*(a (t+2)-a (t+1))*(b (t+1)-b t)| +
        |(a (t+2)-2*a (t+1)+a t)*b t| := abs_add_le _ _
    _ ≤ (|a (t+2)*(b (t+2)-2*b (t+1)+b t)| + |2*(a (t+2)-a (t+1))*(b (t+1)-b t)|) +
        |(a (t+2)-2*a (t+1)+a t)*b t| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hfirst hcross) hlast

theorem etaTwo_log_second_variation (y : ℝ) (hy : 8 ≤ y) :
    Summable (fun n : ℤ => |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
      2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|) ∧
    (∑' n : ℤ, |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
      2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|) ≤
        (72*Real.log (y+2)+192*Real.log 2)/y := by
  have hyp : 0 < y := by linarith
  let f : ℤ → ℝ := fun n => |Real.log ((n:ℝ)+2)*etaTwo (((n:ℝ)+2)/y)-
    2*(Real.log ((n:ℝ)+1)*etaTwo (((n:ℝ)+1)/y))+Real.log (n:ℝ)*etaTwo ((n:ℝ)/y)|
  let d2 : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+2)/y)-2*etaTwo (((n:ℝ)+1)/y)+etaTwo ((n:ℝ)/y)|
  let d1 : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+1)/y)-etaTwo ((n:ℝ)/y)|
  let dc : ℤ → ℝ := fun n => |clippedLog (y/8) ((n:ℝ)+2)-2*clippedLog (y/8) ((n:ℝ)+1)+clippedLog (y/8) n|
  have hd2 := etaTwo_second_variation y hyp
  have hd1 := etaTwo_first_variation y hyp
  have hdc := clippedLog_second_variation (y/8) (by positivity)
  have hmajor : Summable (fun n : ℤ => Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n) :=
    ((hd2.1.mul_left _).add (hd1.1.mul_left _)).add (hdc.1.mul_left _)
  have hpoint : ∀ n, f n ≤ Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n :=
    fun n => etaTwo_log_second_pointwise y n hy
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  calc
    _ ≤ ∑' n : ℤ, (Real.log (y+2)*d2 n+(16/y)*d1 n+(4*Real.log 2)*dc n) := hf.tsum_le_tsum hpoint hmajor
    _ = Real.log (y+2)*(∑' n : ℤ, d2 n)+(16/y)*(∑' n : ℤ, d1 n)+(4*Real.log 2)*(∑' n : ℤ, dc n) := by
      rw [Summable.tsum_add ((hd2.1.mul_left _).add (hd1.1.mul_left _)) (hdc.1.mul_left _),
        Summable.tsum_add (hd2.1.mul_left _) (hd1.1.mul_left _)]
      simp only [tsum_mul_left,d2,d1,dc]
    _ ≤ Real.log (y+2)*(72/y)+(16/y)*(8*Real.log 2)+(4*Real.log 2)*(2/(y/8)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hd2.2 (Real.log_nonneg (by linarith))
        · exact mul_le_mul_of_nonneg_left hd1.2 (by positivity)
      · exact mul_le_mul_of_nonneg_left hdc.2 (by positivity)
    _ = _ := by ring

end HelfgottQuadratic

end

section

open scoped BigOperators
namespace HelfgottQuadratic

theorem integer_sum_eq_expSum (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (hneg : ∀ n < (0:ℤ), a n = 0) (theta : ℝ) :
    (∑' n : ℤ, a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n) =
      Helfgott.expSum (fun n : ℕ => a n) (theta:AddCircle (1:ℝ)) := by
  let z := Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))
  let f : ℤ → ℂ := fun n => a n*z^n
  have hz : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hs : Summable f := summable_twisted a ha z hz
  have hzneg : ∀ n : ℕ, f (-((n:ℤ)+1)) = 0 := by
    intro n
    simp only [f,hneg (-((n:ℤ)+1)) (by omega),zero_mul]
  change (∑' n : ℤ, f n) = _
  rw [tsum_of_nat_of_neg_add_one (hs.comp_injective Nat.cast_injective)
    (hs.comp_injective (by
      intro n m h
      apply Nat.cast_injective (R:=ℤ)
      linarith : Function.Injective (fun n:ℕ => -((n:ℤ)+1))))]
  simp_rw [hzneg]
  rw [tsum_zero,add_zero]
  unfold Helfgott.expSum
  apply tsum_congr
  intro n
  change a n*z^(n:ℤ) = a n*fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  apply congrArg (fun w:ℂ => a n*w)
  change (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^(n:ℤ) =
    fourier (n:ℤ) (theta:AddCircle (1:ℝ))
  rw [fourier_coe_apply,← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem real_sampled_expSum_second_difference (w : ℝ → ℝ)
    (hw : Summable (fun n : ℤ => ‖((w n):ℂ)‖))
    (hneg : ∀ t ≤ (0:ℝ), w t = 0) (theta : ℝ) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖Helfgott.expSum (fun n => ((w (n:ℝ)):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
        ∑' n : ℤ, |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n| := by
  have hn : ∀ n < (0:ℤ), ((w (n:ℝ)):ℂ) = 0 := by
    intro n hn
    rw [hneg _ (by exact_mod_cast (le_of_lt hn)),Complex.ofReal_zero]
  have hh := second_difference_exponential_bound (fun n : ℤ => ((w (n:ℝ)):ℂ)) hw theta
  rw [integer_sum_eq_expSum _ hw hn theta] at hh
  have heq : (∑' n : ℤ, ‖((w ((n-2:ℤ):ℝ)):ℂ)-2*((w ((n-1:ℤ):ℝ)):ℂ)+((w (n:ℝ)):ℂ)‖) =
      ∑' n : ℤ, |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n| := by
    let f : ℤ → ℝ := fun n => |w ((n:ℝ)+2)-2*w ((n:ℝ)+1)+w n|
    have hp : ∀ n : ℤ, ‖((w ((n-2:ℤ):ℝ)):ℂ)-2*((w ((n-1:ℤ):ℝ)):ℂ)+((w (n:ℝ)):ℂ)‖ = f (n-2) := by
      intro n
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_add,
        Complex.norm_real,Real.norm_eq_abs]
      dsimp [f]
      push_cast
      rw [show (n:ℝ)-2+2 = (n:ℝ) by ring,show (n:ℝ)-2+1 = (n:ℝ)-1 by ring]
      congr 1
      ring
    simp_rw [hp]
    exact (Equiv.subRight (2:ℤ)).tsum_eq f
  rw [heq] at hh
  exact hh

theorem sampled_expSum_norm_le (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (hneg : ∀ n < (0:ℤ), a n = 0) (theta : ℝ) :
    ‖Helfgott.expSum (fun n : ℕ => a n) (theta:AddCircle (1:ℝ))‖ ≤ ∑' n : ℤ, ‖a n‖ := by
  rw [← integer_sum_eq_expSum a ha hneg theta]
  have hz : ‖Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have heq : ∀ n : ℤ, ‖a n*(Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖ = ‖a n‖ := by
    intro n
    simp only [norm_mul,norm_zpow,hz,one_zpow,mul_one]
  have hh := norm_tsum_le_tsum_norm (show Summable (fun n : ℤ => ‖a n*
      (Complex.exp (Complex.I*((2*Real.pi*theta:ℝ):ℂ)))^n‖) by simpa only [heq] using ha)
  simpa only [heq] using hh

end HelfgottQuadratic

end

section

open Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_increment_bound (y t : ℝ) (hy : 0 < y) :
    |etaTwo ((t+1)/y)-etaTwo (t/y)| ≤ 20/y := by
  have h4 := clippedLog_increment_bounds (y/4) t (by positivity)
  have h2 := clippedLog_increment_bounds (y/2) t (by positivity)
  have h1 := clippedLog_increment_bounds y t hy
  rw [etaTwo_clippedLog y (t+1) hy,etaTwo_clippedLog y t hy]
  apply abs_le.mpr
  have he4 : 1/(y/4) = 4/y := by ring
  have he2 : 1/(y/2) = 2/y := by ring
  rw [he4] at h4
  rw [he2] at h2
  simp only [div_eq_mul_inv] at h4 h2 h1 ⊢
  constructor <;> linarith [inv_pos.mpr hy]

theorem etaTwo_pair_second_pointwise (y z t : ℝ) (hy : 0 < y) (hz : 0 < z) :
    |etaTwo ((t+2)/y)*etaTwo ((t+2)/z)-2*(etaTwo ((t+1)/y)*etaTwo ((t+1)/z))+
      etaTwo (t/y)*etaTwo (t/z)| ≤
    (4*Real.log 2)*|etaTwo ((t+2)/z)-2*etaTwo ((t+1)/z)+etaTwo (t/z)|+
    (40/y)*|etaTwo ((t+1)/z)-etaTwo (t/z)|+
    (4*Real.log 2)*|etaTwo ((t+2)/y)-2*etaTwo ((t+1)/y)+etaTwo (t/y)| := by
  let a : ℝ → ℝ := fun s => etaTwo (s/y)
  let b : ℝ → ℝ := fun s => etaTwo (s/z)
  have heq : a (t+2)*b (t+2)-2*(a (t+1)*b (t+1))+a t*b t =
      a (t+2)*(b (t+2)-2*b (t+1)+b t)+2*(a (t+2)-a (t+1))*(b (t+1)-b t)+
      (a (t+2)-2*a (t+1)+a t)*b t := by ring
  have hfirst : |a (t+2)*(b (t+2)-2*b (t+1)+b t)| ≤
      (4*Real.log 2)*|b (t+2)-2*b (t+1)+b t| := by
    rw [abs_mul,abs_of_nonneg (etaTwo_nonneg _)]
    exact mul_le_mul_of_nonneg_right (etaTwo_le_log_two _) (abs_nonneg _)
  have hinc : |a (t+2)-a (t+1)| ≤ 20/y := by
    simpa only [a,show t+1+1 = t+2 by ring] using etaTwo_increment_bound y (t+1) hy
  have hcross : |2*(a (t+2)-a (t+1))*(b (t+1)-b t)| ≤ (40/y)*|b (t+1)-b t| := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _ ≤ (2*(20/y))*|b (t+1)-b t| := by gcongr
      _ = _ := by ring
  have hlast : |(a (t+2)-2*a (t+1)+a t)*b t| ≤
      (4*Real.log 2)*|a (t+2)-2*a (t+1)+a t| := by
    rw [abs_mul,abs_of_nonneg (etaTwo_nonneg _)]
    calc
      _ ≤ |a (t+2)-2*a (t+1)+a t| * (4*Real.log 2) :=
        mul_le_mul_of_nonneg_left (etaTwo_le_log_two _) (abs_nonneg _)
      _ = _ := by ring
  change |a (t+2)*b (t+2)-2*(a (t+1)*b (t+1))+a t*b t| ≤ _
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add hfirst hcross) hlast))

theorem etaTwo_pair_second_variation (y z : ℝ) (hy : 0 < y) (hz : 0 < z) :
    Summable (fun n : ℤ => |etaTwo (((n:ℝ)+2)/y)*etaTwo (((n:ℝ)+2)/z)-
      2*(etaTwo (((n:ℝ)+1)/y)*etaTwo (((n:ℝ)+1)/z))+etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z)|) ∧
    (∑' n : ℤ, |etaTwo (((n:ℝ)+2)/y)*etaTwo (((n:ℝ)+2)/z)-
      2*(etaTwo (((n:ℝ)+1)/y)*etaTwo (((n:ℝ)+1)/z))+etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z)|) ≤
      Real.log 2*(608/y+288/z) := by
  let f : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+2)/y)*etaTwo (((n:ℝ)+2)/z)-
      2*(etaTwo (((n:ℝ)+1)/y)*etaTwo (((n:ℝ)+1)/z))+etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z)|
  let d2 : ℝ → ℤ → ℝ := fun w n => |etaTwo (((n:ℝ)+2)/w)-2*etaTwo (((n:ℝ)+1)/w)+etaTwo ((n:ℝ)/w)|
  let d1 : ℤ → ℝ := fun n => |etaTwo (((n:ℝ)+1)/z)-etaTwo ((n:ℝ)/z)|
  have hy2 := etaTwo_second_variation y hy
  have hz2 := etaTwo_second_variation z hz
  have hz1 := etaTwo_first_variation z hz
  have hmajor : Summable (fun n : ℤ => (4*Real.log 2)*d2 z n+(40/y)*d1 n+(4*Real.log 2)*d2 y n) :=
    ((hz2.1.mul_left _).add (hz1.1.mul_left _)).add (hy2.1.mul_left _)
  have hpoint : ∀ n, f n ≤ (4*Real.log 2)*d2 z n+(40/y)*d1 n+(4*Real.log 2)*d2 y n :=
    fun n => etaTwo_pair_second_pointwise y z n hy hz
  have hf : Summable f := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hpoint hmajor
  refine ⟨hf,?_⟩
  change (∑' n : ℤ, f n) ≤ _
  calc
    _ ≤ ∑' n : ℤ, ((4*Real.log 2)*d2 z n+(40/y)*d1 n+(4*Real.log 2)*d2 y n) := hf.tsum_le_tsum hpoint hmajor
    _ = (4*Real.log 2)*(∑' n : ℤ, d2 z n)+(40/y)*(∑' n : ℤ, d1 n)+(4*Real.log 2)*(∑' n : ℤ, d2 y n) := by
      rw [Summable.tsum_add ((hz2.1.mul_left _).add (hz1.1.mul_left _)) (hy2.1.mul_left _),
        Summable.tsum_add (hz2.1.mul_left _) (hz1.1.mul_left _)]
      simp only [tsum_mul_left,d2,d1]
    _ ≤ (4*Real.log 2)*(72/z)+(40/y)*(8*Real.log 2)+(4*Real.log 2)*(72/y) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hz2.2 (by positivity))
        (mul_le_mul_of_nonneg_left hz1.2 (by positivity))) (mul_le_mul_of_nonneg_left hy2.2 (by positivity))
    _ = _ := by ring

end HelfgottQuadratic

end

section

open Helfgott Finset
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_pair_int_summable (y z : ℝ) (hy : 0 < y) :
    Summable (fun n : ℤ => ‖((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)‖) := by
  apply summable_of_ne_finset_zero (s := Icc (1:ℤ) ⌊y⌋)
  intro n hn
  rw [etaTwo_int_support y hy n hn,zero_mul,Complex.ofReal_zero,norm_zero]

theorem etaTwo_pair_expSum_trivial (y z theta : ℝ) (hy : 0 < y) :
    ‖expSum (fun n => ((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log 2)^2*(⌊y⌋₊:ℝ) := by
  have hs := etaTwo_pair_int_summable y z hy
  have hneg : ∀ n < (0:ℤ), ((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ) = 0 := by
    intro n hn
    rw [etaTwo_zero_nonpos _ (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_lt hn)) hy.le),
      zero_mul,Complex.ofReal_zero]
  have hpoint : ∀ n : ℤ, ‖((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)‖ ≤
      (4*Real.log 2)*‖((etaTwo ((n:ℝ)/y)):ℂ)‖ := by
    intro n
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (etaTwo_nonneg _)]
    calc
      _ ≤ etaTwo ((n:ℝ)/y)*(4*Real.log 2) := mul_le_mul_of_nonneg_left (etaTwo_le_log_two _) (etaTwo_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑' n : ℤ, ‖((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)‖ := sampled_expSum_norm_le _ hs hneg theta
    _ ≤ ∑' n : ℤ, (4*Real.log 2)*‖((etaTwo ((n:ℝ)/y)):ℂ)‖ :=
      hs.tsum_le_tsum hpoint ((etaTwo_int_summable y hy).mul_left _)
    _ = (4*Real.log 2)*(∑' n : ℤ, ‖((etaTwo ((n:ℝ)/y)):ℂ)‖) := tsum_mul_left
    _ ≤ (4*Real.log 2)*((4*Real.log 2)*(⌊y⌋₊:ℝ)) :=
      mul_le_mul_of_nonneg_left (etaTwo_int_energy y hy) (by positivity)
    _ = _ := by ring

theorem etaTwo_pair_expSum_quadratic (y z theta : ℝ) (hy : 0 < y) (hz : 0 < z) :
    4*(Real.sin (Real.pi*theta))^2*
      ‖expSum (fun n => ((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
        Real.log 2*(608/y+288/z) := by
  have hn : ∀ t ≤ (0:ℝ), etaTwo (t/y)*etaTwo (t/z) = 0 := by
    intro t ht
    rw [etaTwo_zero_nonpos _ (div_nonpos_of_nonpos_of_nonneg ht hy.le),zero_mul]
  exact (real_sampled_expSum_second_difference (fun t => etaTwo (t/y)*etaTwo (t/z))
    (etaTwo_pair_int_summable y z hy) hn theta).trans (etaTwo_pair_second_variation y z hy hz).2

theorem etaTwo_pair_expSum_quadratic_cap (y z theta : ℝ) (hy : 0 < y) (hz : 0 < z) :
    ‖expSum (fun n => ((etaTwo ((n:ℝ)/y)*etaTwo ((n:ℝ)/z):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      safeCappedSquare ((4*Real.log 2)^2*(⌊y⌋₊:ℝ))
        (Real.log 2*(152/y+72/z)) (Real.pi*theta) := by
  unfold safeCappedSquare
  split_ifs with hsin
  · exact etaTwo_pair_expSum_trivial y z theta hy
  · refine le_min (etaTwo_pair_expSum_trivial y z theta hy) ?_
    apply (le_div_iff₀ (sq_pos_of_ne_zero hsin)).mpr
    have hh := etaTwo_pair_expSum_quadratic y z theta hy hz
    rw [show Real.log 2*(608/y+288/z) = 4*(Real.log 2*(152/y+72/z)) by ring] at hh
    nlinarith

end HelfgottQuadratic

end

section

open Helfgott
open scoped BigOperators
namespace HelfgottQuadratic

theorem etaTwo_pair_scaled_cap (y theta : ℝ) (hy : 0 < y) (C D m n : ℕ)
    (hC : 0 < C) (hm : C ≤ m) (hn : C ≤ n) (hmD : m ≤ D) (hnD : n ≤ D) :
    ‖expSum (fun d => ((etaTwo ((d:ℝ)/(y/(m:ℝ)))*etaTwo ((d:ℝ)/(y/(n:ℝ))):ℝ):ℂ))
      (theta:AddCircle (1:ℝ))‖ ≤
      safeCappedSquare ((4*Real.log 2)^2*y/(C:ℝ)) (224*Real.log 2*(D:ℝ)/y) (Real.pi*theta) := by
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  have hmp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : (4*Real.log 2)^2*(⌊y/(m:ℝ)⌋₊:ℝ) ≤ (4*Real.log 2)^2*y/(C:ℝ) := by
    calc
      _ ≤ (4*Real.log 2)^2*(y/(m:ℝ)) := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (sq_nonneg _)
      _ ≤ (4*Real.log 2)^2*(y/(C:ℝ)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hy.le hCp (by exact_mod_cast hm)) (sq_nonneg _)
      _ = _ := by ring
  have hB : Real.log 2*(152/(y/(m:ℝ))+72/(y/(n:ℝ))) ≤ 224*Real.log 2*(D:ℝ)/y := by
    calc
      _ = Real.log 2*(152*(m:ℝ)+72*(n:ℝ))/y := by field_simp
      _ ≤ Real.log 2*(152*(D:ℝ)+72*(D:ℝ))/y := by gcongr
      _ = _ := by ring
  apply (etaTwo_pair_expSum_quadratic_cap _ _ theta (div_pos hy hmp) (div_pos hy hnp)).trans
  unfold safeCappedSquare
  split_ifs
  · exact hA
  · exact min_le_min hA (div_le_div_of_nonneg_right hB (sq_nonneg _))

end HelfgottQuadratic

end

section
/- Finite Cauchy-Schwarz, correlation and Schur proofs retained from
accepted Prove2Me submission dc167013-7b1b-47a5-bd68-36e63ad77223,
by raresbuhai, Apache 2.0. -/
open Finset
open scoped BigOperators ComplexConjugate
namespace HelfgottQuadratic
lemma finite_complex_cauchy_square {ι : Type*} (s : Finset ι) (a F : ι → ℂ) :
    ‖∑ d ∈ s,a d*F d‖^2 ≤ (∑ d ∈ s,‖a d‖^2)*(∑ d ∈ s,‖F d‖^2) := by
  have ht : ‖∑ d ∈ s,a d*F d‖ ≤ ∑ d ∈ s,‖a d‖*‖F d‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun d => a d*F d)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans (sum_mul_sq_le_sq_mul_sq s (fun d => ‖a d‖) (fun d => ‖F d‖))

lemma finite_correlation_energy_identity {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) :
    ((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ) =
      ∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n)) := by
  have hz (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z*conj z := by
    rw [Complex.sq_norm,Complex.mul_conj]
  simp_rw [Complex.ofReal_sum,hz,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma finite_correlation_energy_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    (∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2) ≤
      ∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n := by
  have h0 : 0 ≤ ∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ = ‖((∑ d ∈ D,‖∑ m ∈ M,b m*K d m‖^2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]
    _ = ‖∑ m ∈ M,∑ n ∈ M,b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      rw [finite_correlation_energy_identity]
    _ ≤ ∑ m ∈ M,∑ n ∈ M,‖b m*conj (b n)*(∑ d ∈ D,K d m*conj (K d n))‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul,Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hC m hm n hn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma finite_bilinear_correlation_bound {ι κ : Type*} (D : Finset ι) (M : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (K : ι → κ → ℂ) (C : κ → κ → ℝ)
    (hC : ∀ m ∈ M,∀ n ∈ M,‖∑ d ∈ D,K d m*conj (K d n)‖ ≤ C m n) :
    ‖∑ d ∈ D,∑ m ∈ M,a d*b m*K d m‖^2 ≤
      (∑ d ∈ D,‖a d‖^2)*(∑ m ∈ M,∑ n ∈ M,‖b m‖*‖b n‖*C m n) := by
  have hc := finite_complex_cauchy_square D a (fun d => ∑ m ∈ M,b m*K d m)
  have he : (∑ d ∈ D,a d*(∑ m ∈ M,b m*K d m)) =
      ∑ d ∈ D,∑ m ∈ M,a d*b m*K d m := by
    simp_rw [Finset.mul_sum,mul_assoc]
  rw [he] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (finite_correlation_energy_bound D M b K C hC)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

lemma symmetric_finite_correlation_schur {ι : Type*} (M : Finset ι) (u : ι → ℝ)
    (C : ι → ι → ℝ) (R : ℝ) (hC : ∀ m n,0 ≤ C m n)
    (hsym : ∀ m n,C m n=C n m)
    (hrow : ∀ m ∈ M,(∑ n ∈ M,C m n) ≤ R) :
    (∑ m ∈ M,∑ n ∈ M,u m*u n*C m n) ≤ R*(∑ m ∈ M,(u m)^2) := by
  have hp : (∑ m ∈ M,∑ n ∈ M,(2*u m*u n)*C m n) ≤
      ∑ m ∈ M,∑ n ∈ M,((u m)^2+(u n)^2)*C m n := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (u m-u n)]) (hC m n)
  have hleft : (∑ m ∈ M,∑ n ∈ M,(2*u m*u n)*C m n) =
      2*(∑ m ∈ M,∑ n ∈ M,u m*u n*C m n) := by
    simp_rw [show ∀ m n,(2*u m*u n)*C m n = 2*(u m*u n*C m n) by intro m n;ring,←Finset.mul_sum]
  have hright : (∑ m ∈ M,∑ n ∈ M,((u m)^2+(u n)^2)*C m n) =
      2*(∑ m ∈ M,(u m)^2*(∑ n ∈ M,C m n)) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    have he : (∑ m ∈ M,∑ n ∈ M,(u n)^2*C m n) =
        ∑ m ∈ M,∑ n ∈ M,(u m)^2*C m n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [hsym n m]
    rw [he]
    simp_rw [←Finset.mul_sum]
    ring
  have hr : (∑ m ∈ M,(u m)^2*(∑ n ∈ M,C m n)) ≤ R*(∑ m ∈ M,(u m)^2) := by
    calc
      _ ≤ ∑ m ∈ M,(u m)^2*R := Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _))
      _ = _ := by rw [←Finset.sum_mul];ring
  rw [hleft,hright] at hp
  linarith


end HelfgottQuadratic

end

section

open Helfgott Finset
open scoped BigOperators ComplexConjugate
namespace HelfgottQuadratic

noncomputable def smoothBilinearKernel (y theta : ℝ) (d m : ℕ) : ℂ :=
  ((etaTwo (((d*m:ℕ):ℝ)/y)):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ))

/- The Fourier product identity follows the accepted finite-correlation proof
dc167013-7b1b-47a5-bd68-36e63ad77223 by raresbuhai (Apache 2.0). -/
theorem fourier_product_correlation (alpha : AddCircle (1:ℝ)) (d m n : ℕ) :
    fourier ((d*m:ℕ):ℤ) alpha*conj (fourier ((d*n:ℕ):ℤ) alpha) =
      fourier (d:ℤ) (((m:ℤ)-(n:ℤ)) • alpha) := by
  rw [←fourier_neg,←fourier_add]
  have he : ((d*m:ℕ):ℤ)+ -((d*n:ℕ):ℤ) = (d:ℤ)*((m:ℤ)-(n:ℤ)) := by push_cast; ring
  rw [he]
  simp only [fourier_apply,smul_smul]

theorem smoothBilinearKernel_product (y theta : ℝ) (d m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    smoothBilinearKernel y theta d m*conj (smoothBilinearKernel y theta d n) =
      ((etaTwo ((d:ℝ)/(y/(m:ℝ)))*etaTwo ((d:ℝ)/(y/(n:ℝ))):ℝ):ℂ)*
        fourier (d:ℤ) (((m:ℝ)-(n:ℝ))*theta:AddCircle (1:ℝ)) := by
  have hmp : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
  have hnp : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hem : ((d*m:ℕ):ℝ)/y = (d:ℝ)/(y/(m:ℝ)) := by push_cast; field_simp
  have hen : ((d*n:ℕ):ℝ)/y = (d:ℝ)/(y/(n:ℝ)) := by push_cast; field_simp
  unfold smoothBilinearKernel
  rw [map_mul,Complex.conj_ofReal,hem,hen,Complex.ofReal_mul]
  rw [show ((etaTwo ((d:ℝ)/(y/(m:ℝ))):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ)))*
      ((etaTwo ((d:ℝ)/(y/(n:ℝ))):ℂ)*conj (fourier ((d*n:ℕ):ℤ) (theta:AddCircle (1:ℝ)))) =
      ((etaTwo ((d:ℝ)/(y/(m:ℝ))):ℂ)*(etaTwo ((d:ℝ)/(y/(n:ℝ))):ℂ))*
      (fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ))*conj (fourier ((d*n:ℕ):ℤ) (theta:AddCircle (1:ℝ)))) by ring]
  rw [fourier_product_correlation,← AddCircle.coe_zsmul]
  simp only [zsmul_eq_mul,Int.cast_sub,Int.cast_natCast]

theorem smoothBilinearKernel_support (y theta : ℝ) (hy : 0 < y) (C d m : ℕ)
    (hC : 0 < C) (hm : C ≤ m) (hd : d ∉ Icc 1 ⌊y/(C:ℝ)⌋₊) :
    smoothBilinearKernel y theta d m = 0 := by
  have hCp : (0:ℝ) < C := by exact_mod_cast hC
  by_cases hd0 : d = 0
  · subst d
    simp [smoothBilinearKernel,etaTwo_zero_nonpos 0 le_rfl]
  · have hdf : ⌊y/(C:ℝ)⌋₊ < d := by simp only [mem_Icc,not_and_or,not_le] at hd; omega
    have hdy : y/(C:ℝ) ≤ (d:ℝ) := by
      have hh : (⌊y/(C:ℝ)⌋₊:ℝ)+1 ≤ d := by exact_mod_cast hdf
      linarith [Nat.lt_floor_add_one (y/(C:ℝ))]
    have hym : y ≤ ((d*m:ℕ):ℝ) := by
      have hh := (div_le_iff₀ hCp).mp hdy
      have hmc : (C:ℝ) ≤ m := by exact_mod_cast hm
      push_cast
      exact hh.trans (mul_le_mul_of_nonneg_left hmc (Nat.cast_nonneg d))
    simp only [smoothBilinearKernel,etaTwo_zero_large y _ hy hym,Complex.ofReal_zero,zero_mul]

theorem smoothBilinearKernel_correlation (y theta : ℝ) (hy : 0 < y) (C D m n : ℕ)
    (hC : 0 < C) (hm : C ≤ m) (hn : C ≤ n) (hmD : m ≤ D) (hnD : n ≤ D) :
    ‖∑ d ∈ Icc 1 ⌊y/(C:ℝ)⌋₊, smoothBilinearKernel y theta d m*conj (smoothBilinearKernel y theta d n)‖ ≤
      safeCappedSquare ((4*Real.log 2)^2*y/(C:ℝ)) (224*Real.log 2*(D:ℝ)/y)
        (Real.pi*((m:ℝ)-(n:ℝ))*theta) := by
  have hmp : 0 < m := by omega
  have hnp : 0 < n := by omega
  have hsum : (∑ d ∈ Icc 1 ⌊y/(C:ℝ)⌋₊, smoothBilinearKernel y theta d m*conj (smoothBilinearKernel y theta d n)) =
      expSum (fun d => ((etaTwo ((d:ℝ)/(y/(m:ℝ)))*etaTwo ((d:ℝ)/(y/(n:ℝ))):ℝ):ℂ))
        (((m:ℝ)-(n:ℝ))*theta:AddCircle (1:ℝ)) := by
    unfold expSum
    rw [tsum_eq_sum (s:=Icc 1 ⌊y/(C:ℝ)⌋₊) (fun d hd => by
      rw [← smoothBilinearKernel_product y theta d m n hmp hnp,
        smoothBilinearKernel_support y theta hy C d m hC hm hd,zero_mul])]
    exact sum_congr rfl (fun d hd => smoothBilinearKernel_product y theta d m n hmp hnp)
  rw [hsum]
  simpa only [mul_assoc] using
    etaTwo_pair_scaled_cap y (((m:ℝ)-(n:ℝ))*theta) hy C D m n hC hm hn hmD hnD

end HelfgottQuadratic

end

section

open Helfgott Finset
open scoped BigOperators ComplexConjugate
namespace HelfgottQuadratic

theorem smooth_bilinear_quadratic_energy (y theta beta : ℝ) (hy : 0 < y)
    (C D q : ℕ) (hC : 0 < C) (hq : 2 ≤ q) (a : ℤ) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2)
    (u v : ℕ → ℂ) :
    let A := (4*Real.log 2)^2*y/(C:ℝ)
    let B := 224*Real.log 2*(D:ℝ)/y
    ‖∑ d ∈ Icc 1 ⌊y/(C:ℝ)⌋₊, ∑ m ∈ Ico C D,
      u d*v m*((etaTwo (((d*m:ℕ):ℝ)/y):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ)))‖^2 ≤
      (∑ d ∈ Icc 1 ⌊y/(C:ℝ)⌋₊, ‖u d‖^2)*(∑ m ∈ Ico C D, ‖v m‖^2)*
        (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B))) := by
  let A := (4*Real.log 2)^2*y/(C:ℝ)
  let B := 224*Real.log 2*(D:ℝ)/y
  let R := (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B)))
  let K : ℕ → ℕ → ℝ := fun m n => safeCappedSquare A B (Real.pi*((m:ℝ)-(n:ℝ))*theta)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : ∀ m n, 0 ≤ K m n := fun m n => safeCappedSquare_nonneg A B _ hA hB
  have hsym : ∀ m n, K m n = K n m := by
    intro m n
    dsimp [K]
    rw [show Real.pi*((m:ℝ)-(n:ℝ))*theta = -(Real.pi*((n:ℝ)-(m:ℝ))*theta) by ring,
      safeCappedSquare_neg]
  have hrow : ∀ m ∈ Ico C D, (∑ n ∈ Ico C D, K m n) ≤ R := by
    intro m hm
    simp_rw [hsym m]
    exact quadratic_rational_interval_row a q C D hq haq theta beta m A B htheta hbeta hA hB
  have hcorr : ∀ m ∈ Ico C D, ∀ n ∈ Ico C D,
      ‖∑ d ∈ Icc 1 ⌊y/(C:ℝ)⌋₊,
        smoothBilinearKernel y theta d m*conj (smoothBilinearKernel y theta d n)‖ ≤ K m n := by
    intro m hm n hn
    exact smoothBilinearKernel_correlation y theta hy C D m n hC (mem_Ico.mp hm).1 (mem_Ico.mp hn).1
      (mem_Ico.mp hm).2.le (mem_Ico.mp hn).2.le
  have hc := finite_bilinear_correlation_bound (Icc 1 ⌊y/(C:ℝ)⌋₊) (Ico C D)
    u v (smoothBilinearKernel y theta) K hcorr
  have hs := symmetric_finite_correlation_schur (Ico C D) (fun m => ‖v m‖) K R hK hsym hrow
  have hh := hc.trans (mul_le_mul_of_nonneg_left hs (sum_nonneg (fun d hd => sq_nonneg _)))
  apply hh.trans_eq
  dsimp only [R,A,B]
  ring

end HelfgottQuadratic

end

section
/- Arithmetic energy proofs retained from accepted Prove2Me submission
dc167013-7b1b-47a5-bd68-36e63ad77223 by raresbuhai, Apache 2.0. -/
open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace HelfgottQuadratic
theorem finite_divisor_weight_square_energy (M U : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ) := by
  have hpoint (n : ℕ) : (∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        if Nat.lcm d e ∣ n then c d*c e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;>
      simp [hdvd,hevd,Nat.lcm_dvd_iff]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul]
  have hi : (Finset.Icc 1 M).filter (fun n => Nat.lcm d e ∣ n) =
      (Finset.Ioc 0 M).filter (fun n => Nat.lcm d e ∣ n) := by
    congr 1
  rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
  ring


lemma arithmeticTail_zero_of_le (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    arithmeticTail U f n = 0 := by
  change f n-(if n ≤ U then f n else 0) = 0
  simp [hn]

lemma arithmeticTail_self_of_gt (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : U < n) :
    arithmeticTail U f n = f n := by
  change f n-(if n ≤ U then f n else 0) = f n
  simp [not_le_of_gt hn]

lemma vaughan_bilinear_coefficient_zero (U n : ℕ) (hn : n ≤ U) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  exact arithmeticTail_zero_of_le U d _ (hdn.trans hn)

lemma vaughan_bilinear_coefficient_short_moebius (U n : ℕ) (hn : n ≠ 1) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n =
      -(∑ d ∈ n.divisors.filter (fun d => d ≤ U), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have he : arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta =
      1-arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta := by
    unfold arithmeticTail
    rw [sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [he]
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply_ne hn,zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
  congr 1


lemma short_moebius_divisor_sum (U n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ U),((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  have he : n.divisors.filter (fun d => d ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hdU⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hdU⟩,hd⟩
    · rintro ⟨⟨hdpos,hdU⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hdU⟩
  rw [he,Finset.sum_filter]

lemma vaughan_mobius_energy_pointwise (U n : ℕ) (hU : 1 ≤ U) (hn : 0 < n) :
    ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n)^2 =
      (∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
      (if n=1 then 1 else 0) := by
  by_cases hn1 : n=1
  · subst n
    rw [vaughan_bilinear_coefficient_zero U 1 hU]
    have hs : (∑ d ∈ Finset.Icc 1 U,if d ∣ 1 then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 1 := by
      rw [←short_moebius_divisor_sum U 1 (by norm_num)]
      rw [Nat.divisors_one,Finset.filter_singleton]
      simp [hU]
    rw [hs]
    norm_num
  · rw [vaughan_bilinear_coefficient_short_moebius U n hn1,short_moebius_divisor_sum U n hn,if_neg hn1]
    ring

theorem vaughan_mobius_tail_square_energy (U M : ℕ) (hU : 1 ≤ U) :
    (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)*
        ((M/(Nat.lcm d e) : ℕ) : ℝ))-(if 1 ≤ M then 1 else 0) := by
  have hs : (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) := by
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hm).1;omega,(Finset.mem_Icc.mp hm).2⟩
    · intro m hm hnot
      have hmU : m ≤ U := by
        have hml := (Finset.mem_Icc.mp hm).1
        have hmh := (Finset.mem_Icc.mp hm).2
        have hnot' : ¬(U+1 ≤ m ∧ m ≤ M) := by simpa only [Finset.mem_Icc] using hnot
        omega
      rw [vaughan_bilinear_coefficient_zero U m hmU]
      simp
  rw [hs]
  have he : (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      ∑ m ∈ Finset.Icc 1 M,
        ((∑ d ∈ Finset.Icc 1 U,if d ∣ m then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
          (if m=1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vaughan_mobius_energy_pointwise U m hU (Finset.mem_Icc.mp hm).1
  rw [he,Finset.sum_sub_distrib,finite_divisor_weight_square_energy]
  congr 1
  simp only [Finset.sum_ite_eq',Finset.mem_Icc]
  simp


lemma nat_div_cast_error_le_one (M k : ℕ) (hk : 0 < k) :
    |((M/k : ℕ) : ℝ)-(M : ℝ)/(k : ℝ)| ≤ 1 := by
  have hlo : ((M/k : ℕ) : ℝ) ≤ (M : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hmod : ((M%k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt M hk
  have he : (k : ℝ)*((M/k : ℕ) : ℝ)+((M%k : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast Nat.div_add_mod M k
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hupper : (M : ℝ)/(k : ℝ) ≤ ((M/k : ℕ) : ℝ)+1 := (div_le_iff₀ hkR).mpr (by nlinarith)
  linarith

theorem finite_divisor_weight_square_energy_approximation (M U : ℕ) (c : ℕ → ℝ) :
    |(∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ))| ≤
        (∑ d ∈ Finset.Icc 1 U,|c d|)^2 := by
  rw [finite_divisor_weight_square_energy]
  have he : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ))-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U,|∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,|c d| * |c e| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      have hk : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      rw [abs_mul,abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (nat_div_cast_error_le_one M _ hk)
    _ = _ := by rw [pow_two,Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;rw [Finset.mul_sum]

theorem finite_divisor_weight_leading_quadratic_nonneg (U : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ) := by
  let M := U.factorial
  have hM : (0:ℝ)<M := by exact_mod_cast Nat.factorial_pos U
  have hexact : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ)) =
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdM : d ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    have heM : e ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
    rw [Nat.cast_div (Nat.lcm_dvd hdM heM)] <;> try exact_mod_cast (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).ne'
    ring
  have h := finite_divisor_weight_square_energy M U c
  rw [hexact] at h
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hM


theorem vaughan_mobius_tail_energy_asymptotic (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := by
  refine ⟨finite_divisor_weight_leading_quadratic_nonneg U _,?_⟩
  have hsum : (∑ d ∈ Finset.Icc 1 U,|((ArithmeticFunction.moebius d : ℤ) : ℝ)|) ≤ (U : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 U,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      _ = _ := by simp
  have h := finite_divisor_weight_square_energy_approximation M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  have he := vaughan_mobius_tail_square_energy U M hU
  have hfull := finite_divisor_weight_square_energy M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  rw [hfull] at h
  rw [he,sub_add_cancel]
  refine h.trans ?_
  nlinarith [Finset.sum_nonneg (fun d (_ : d ∈ Finset.Icc 1 U) => abs_nonneg (((ArithmeticFunction.moebius d : ℤ) : ℝ)))]


theorem vonMangoldt_square_interval_energy (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (∑ d ∈ Finset.Ico A B,(vonMangoldt d)^2) ≤
      Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)) := by
  have hBR : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBR
  have hpoint (d : ℕ) (hd : d ∈ Finset.Ico A B) :
      (vonMangoldt d)^2 ≤ Real.log (B : ℝ)*vonMangoldt d := by
    have hdpos : (0:ℝ)<d := by exact_mod_cast (show 0<d from by have := (Finset.mem_Ico.mp hd).1;omega)
    have hdB : (d : ℝ) ≤ B := by exact_mod_cast (Finset.mem_Ico.mp hd).2.le
    have hl := (vonMangoldt_le_log (n := d)).trans (Real.log_le_log hdpos hdB)
    nlinarith [vonMangoldt_nonneg (n := d)]
  have hsubset : Finset.Ico A B ⊆ Finset.Icc 1 B := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨hA.trans (Finset.mem_Ico.mp hd).1,(Finset.mem_Ico.mp hd).2.le⟩
  have hpsi : (∑ d ∈ Finset.Icc 1 B,vonMangoldt d) = Chebyshev.psi (B : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨by omega,(Finset.mem_Icc.mp hd).2⟩
    · intro d hd hnot
      have hd0 : d=0 := by
        have hdB := (Finset.mem_Icc.mp hd).2
        have hnot' : ¬(1 ≤ d ∧ d ≤ B) := by simpa only [Finset.mem_Icc] using hnot
        omega
      subst d
      simp
  calc
    _ ≤ ∑ d ∈ Finset.Ico A B,Real.log (B : ℝ)*vonMangoldt d := Finset.sum_le_sum hpoint
    _ = Real.log (B : ℝ)*(∑ d ∈ Finset.Ico A B,vonMangoldt d) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log (B : ℝ)*(∑ d ∈ Finset.Icc 1 B,vonMangoldt d) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => vonMangoldt_nonneg)) hlogB
    _ = Real.log (B : ℝ)*Chebyshev.psi (B : ℝ) := by rw [hpsi]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.psi_le hBR) hlogB


lemma vaughan_mobius_interval_energy_upper (U C D : ℕ) (hU : 1 ≤ U) (hC : U+1 ≤ C) :
    (∑ m ∈ Finset.Ico C D,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) ≤
      (D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2 := by
  have hsubset : Finset.Ico C D ⊆ Finset.Icc (U+1) D := by
    intro m hm
    exact Finset.mem_Icc.mpr ⟨hC.trans (Finset.mem_Ico.mp hm).1,(Finset.mem_Ico.mp hm).2.le⟩
  have h := (vaughan_mobius_tail_energy_asymptotic U D hU).2
  have hupper := (le_abs_self _).trans h
  have hδ : (0:ℝ) ≤ (if 1 ≤ D then 1 else 0) := by split_ifs <;> norm_num
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => sq_nonneg _)).trans ?_
  linarith


end HelfgottQuadratic

end

section

open Helfgott Finset ArithmeticFunction
open scoped BigOperators
namespace HelfgottQuadratic

theorem arithmeticTail_vonMangoldt_energy (V T : ℕ) :
    (∑ d ∈ Icc 1 T, ‖((arithmeticTail V vonMangoldt d:ℝ):ℂ)‖^2) ≤
      Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)) := by
  have hpoint : ∀ d ∈ Icc 1 T, ‖((arithmeticTail V vonMangoldt d:ℝ):ℂ)‖^2 ≤ (vonMangoldt d)^2 := by
    intro d hd
    by_cases hdV : d ≤ V
    · rw [arithmeticTail_zero_of_le V d _ hdV,Complex.ofReal_zero,norm_zero,zero_pow (by decide)]
      exact sq_nonneg _
    · rw [arithmeticTail_self_of_gt V d _ (by omega),Complex.norm_real,Real.norm_eq_abs,sq_abs]
  apply (sum_le_sum hpoint).trans
  rw [← Ico_add_one_right_eq_Icc]
  exact vonMangoldt_square_interval_energy 1 (T+1) le_rfl (by omega)

theorem vaughan_typeTwo_quadratic_block (U V C D q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hU : 1 ≤ U) (hC : U+1 ≤ C) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (hy : 0 < y) (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let T := ⌊y/(C:ℝ)⌋₊
    let A := (4*Real.log 2)^2*y/(C:ℝ)
    let B := 224*Real.log 2*(D:ℝ)/y
    ‖∑ d ∈ Icc 1 T, ∑ m ∈ Ico C D,
      ((arithmeticTail V vonMangoldt d:ℝ):ℂ)*
      (((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m:ℝ):ℂ)*
      ((etaTwo (((d*m:ℕ):ℝ)/y):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ)))‖^2 ≤
      (Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)))*
      ((D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
        ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2)*
      (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B))) := by
  let T := ⌊y/(C:ℝ)⌋₊
  let A := (4*Real.log 2)^2*y/(C:ℝ)
  let B := 224*Real.log 2*(D:ℝ)/y
  let u : ℕ → ℂ := fun d => ((arithmeticTail V vonMangoldt d:ℝ):ℂ)
  let v : ℕ → ℂ := fun m => (((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m:ℝ):ℂ)
  have hCp : 0 < C := by omega
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ 2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B)) := by positivity
  have hv : (∑ m ∈ Ico C D, ‖v m‖^2) ≤
      (D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
        ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2 := by
    simpa only [v,Complex.norm_real,Real.norm_eq_abs,sq_abs] using vaughan_mobius_interval_energy_upper U C D hU hC
  have hv0 := (sum_nonneg (fun m (_:m∈Ico C D) => sq_nonneg ‖v m‖)).trans hv
  have hu := arithmeticTail_vonMangoldt_energy V T
  have hu0 := (sum_nonneg (fun d (_:d∈Icc 1 T) => sq_nonneg ‖u d‖)).trans hu
  have hh := smooth_bilinear_quadratic_energy y theta beta hy C D q hCp hq a haq htheta hbeta u v
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ hR
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hu hv (sum_nonneg (fun m hm => sq_nonneg _)) hu0

end HelfgottQuadratic

end

open Helfgott Finset ArithmeticFunction
theorem solution (U V C D q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hU : 1 ≤ U) (hC : U+1 ≤ C) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (hy : 0 < y) (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let T := ⌊y/(C:ℝ)⌋₊
    let A := (4*Real.log 2)^2*y/(C:ℝ)
    let B := 224*Real.log 2*(D:ℝ)/y
    ‖∑ d ∈ Icc 1 T, ∑ m ∈ Ico C D,
      ((arithmeticTail V vonMangoldt d:ℝ):ℂ)*
      (((arithmeticTail U (moebius:ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m:ℝ):ℂ)*
      ((etaTwo (((d*m:ℕ):ℝ)/y):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ)))‖^2 ≤
      (Real.log (T+1:ℕ)*(Real.log 4*(T+1:ℕ)+2*Real.sqrt (T+1:ℕ)*Real.log (T+1:ℕ)))*
      ((D:ℝ)*(∑ d ∈ Icc 1 U, ∑ e ∈ Icc 1 U,
        ((moebius d:ℤ):ℝ)*((moebius e:ℤ):ℝ)/(Nat.lcm d e:ℝ))+(U:ℝ)^2)*
      (((D-C)/q+1:ℕ):ℝ)*(2*A+min (2*B*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*B))) := by
  exact HelfgottQuadratic.vaughan_typeTwo_quadratic_block U V C D q a y theta beta hU hC hq haq hy htheta hbeta
