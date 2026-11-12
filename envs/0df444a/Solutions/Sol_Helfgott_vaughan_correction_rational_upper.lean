-- Prove2me | solution 1 for Helfgott.vaughan_correction_rational_upper
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T18:06:52.155468+00:00
-- url     : https://prove2.me/submissions/db6aed16-7a48-44e3-9490-4663c990880c

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
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
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

namespace HelfgottQuadratic

theorem rational_small_divisor_sine (a : ℤ) (q d : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (hd : 0 < d) (hdq : 2*d ≤ q)
    (theta beta : ℝ) (htheta : theta = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    1/(q:ℝ) ≤ |Real.sin (Real.pi*((d:ℝ)*theta))| := by
  let r : ℤ := round ((d:ℝ)*theta)
  let z : ℤ := a*(d:ℤ)-(q:ℤ)*r
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hz : z ≠ 0 := by
    intro hz
    have heq : a*(d:ℤ) = (q:ℤ)*r := sub_eq_zero.mp hz
    have hdiv : (q:ℤ) ∣ a*(d:ℤ) := ⟨r,heq⟩
    have hdivNat : q ∣ a.natAbs*d := by
      simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdiv
    have hqd : q ∣ d := haq.symm.dvd_of_dvd_mul_left hdivNat
    have hle := Nat.le_of_dvd hd hqd
    omega
  have hz1 : (1:ℝ) ≤ |(z:ℝ)| := by
    have hh : (1:ℤ) ≤ |z| := by have := abs_pos.mpr hz; omega
    exact_mod_cast hh
  have hrepr : (z:ℝ) = (q:ℝ)*((d:ℝ)*theta-(r:ℝ))-(q:ℝ)*beta*(d:ℝ) := by
    dsimp [z]
    push_cast
    rw [htheta]
    field_simp
    ring
  have herr : (q:ℝ)*|beta| * (d:ℝ) ≤ 1/2 := by
    calc
      _ ≤ (q:ℝ)*(1/(q:ℝ)^2)*(d:ℝ) := by gcongr
      _ = (d:ℝ)/(q:ℝ) := by field_simp
      _ ≤ 1/2 := (div_le_iff₀ hq0).mpr (by
        have hh : 2*(d:ℝ) ≤ q := by exact_mod_cast hdq
        linarith)
  have hdist : 1/(2*(q:ℝ)) ≤ |(d:ℝ)*theta-(r:ℝ)| := by
    have hh := abs_sub ((q:ℝ)*((d:ℝ)*theta-(r:ℝ))) ((q:ℝ)*beta*(d:ℝ))
    rw [← hrepr] at hh
    simp only [abs_mul,abs_of_nonneg hq0.le,abs_of_nonneg hd0.le] at hh
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*(q:ℝ))).mpr
    nlinarith
  have hres : |(d:ℝ)*theta-(r:ℝ)| ≤ 1/2 := abs_sub_round _
  have hangle : Real.pi*|(d:ℝ)*theta-(r:ℝ)| ≤ Real.pi/2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin (by positivity : 0 ≤ Real.pi*|(d:ℝ)*theta-(r:ℝ)|) hangle
  have hlinear : 2*|(d:ℝ)*theta-(r:ℝ)| ≤ Real.sin (Real.pi*|(d:ℝ)*theta-(r:ℝ)|) := by
    convert hsin using 1 <;> field_simp
  rw [abs_sin_pi_eq_sin_pi_abs_sub_round]
  change 1/(q:ℝ) ≤ Real.sin (Real.pi*|(d:ℝ)*theta-(r:ℝ)|)
  have hdist' : 1/(q:ℝ) ≤ 2*|(d:ℝ)*theta-(r:ℝ)| := by
    have heq : 1/(q:ℝ) = 2*(1/(2*(q:ℝ))) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hdist (by norm_num)
  exact hdist'.trans hlinear

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

open scoped BigOperators
namespace Helfgott

theorem etaTwo_expSum_finite (y theta : ℝ) (hy : 0 < y) :
    expSum (fun n => ((etaTwo ((n:ℝ)/y)):ℂ)) (theta:AddCircle (1:ℝ)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((etaTwo ((n:ℝ)/y)):ℂ)*fourier (n:ℤ) (theta:AddCircle (1:ℝ)) := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  have hz : etaTwo ((n:ℝ)/y) = 0 := by
    by_cases hn0 : n = 0
    · subst n
      simp [etaTwo]
    · have hny : ⌊y⌋₊ < n := by simp only [Finset.mem_Icc,not_and_or,not_le] at hn; omega
      exact HelfgottQuadratic.etaTwo_zero_large y n hy (Nat.lt_of_floor_lt hny).le
  simp [hz]

theorem etaTwo_product_expSum (d : ℕ) (hd : 0 < d) (y theta : ℝ) (hy : 0 < y) :
    (∑ m ∈ Finset.Icc 1 ⌊y/(d:ℝ)⌋₊,
      ((etaTwo (((d*m:ℕ):ℝ)/y)):ℂ)*fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ))) =
      expSum (fun m => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)) ((d:ℝ)*theta:AddCircle (1:ℝ)) := by
  rw [etaTwo_expSum_finite _ _ (div_pos hy (by exact_mod_cast hd))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [etaTwo_product_scale d m hd y hy]
  apply congrArg (fun z:ℂ => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)*z)
  rw [fourier_coe_apply,fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem vaughan_correction_quadratic_cancellation (U V : ℕ) (y theta : ℝ) (hy : 0 < y) :
    ‖expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      ∑ d ∈ Finset.Icc 1 (min (U*V) ⌊y⌋₊), Real.log (d:ℝ)*
        (if Real.sin (Real.pi*((d:ℝ)*theta)) = 0 then (4*Real.log 2)*(⌊y/(d:ℝ)⌋₊:ℝ)
        else min ((4*Real.log 2)*(⌊y/(d:ℝ)⌋₊:ℝ))
          (18/((y/(d:ℝ))*(Real.sin (Real.pi*((d:ℝ)*theta)))^2))) := by
  rw [vaughan_correction_expSum U V y hy]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdp : 0 < d := by omega
  rw [etaTwo_product_expSum d hdp y theta hy,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right (vaughan_correction_coefficient_abs_le U V d) (norm_nonneg _)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hd1))
  exact HelfgottQuadratic.etaTwo_expSum_quadratic_cap (y/(d:ℝ)) ((d:ℝ)*theta)
    (div_pos hy (by exact_mod_cast hdp))

end Helfgott

end

section

open scoped BigOperators
namespace Helfgott

theorem etaTwo_variable_scale_cap (y theta : ℝ) (hy : 0 < y) (d D Q : ℕ)
    (hlo : D+1 ≤ d) (hhi : d ≤ D+Q) :
    ‖expSum (fun m => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)) ((d:ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      HelfgottQuadratic.safeCappedSquare ((4*Real.log 2)*y/(D+1:ℕ))
        (18*(D+Q:ℕ)/y) (Real.pi*((d:ℝ)*theta)) := by
  have hd : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hD : (0:ℝ) < (D+1:ℕ) := by positivity
  have hy' : 0 < y/(d:ℝ) := div_pos hy hd
  have hlog : 0 ≤ 4*Real.log 2 := by positivity
  have htriv : ‖expSum (fun m => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)) ((d:ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      (4*Real.log 2)*y/(D+1:ℕ) := by
    calc
      _ ≤ (4*Real.log 2)*(⌊y/(d:ℝ)⌋₊:ℝ) := HelfgottQuadratic.etaTwo_expSum_trivial _ _ hy'
      _ ≤ (4*Real.log 2)*(y/(d:ℝ)) := mul_le_mul_of_nonneg_left (Nat.floor_le hy'.le) hlog
      _ ≤ (4*Real.log 2)*(y/(D+1:ℕ)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hy.le hD (by exact_mod_cast hlo)) hlog
      _ = _ := by ring
  unfold HelfgottQuadratic.safeCappedSquare
  by_cases hs : Real.sin (Real.pi*((d:ℝ)*theta)) = 0
  · rw [if_pos hs]
    exact htriv
  · rw [if_neg hs]
    refine le_min htriv ?_
    have hh := HelfgottQuadratic.etaTwo_expSum_quadratic_cap (y/(d:ℝ)) ((d:ℝ)*theta) hy'
    rw [if_neg hs] at hh
    calc
      _ ≤ 18/((y/(d:ℝ))*(Real.sin (Real.pi*((d:ℝ)*theta)))^2) := hh.trans (min_le_right _ _)
      _ = (18*(d:ℝ)/y)/(Real.sin (Real.pi*((d:ℝ)*theta)))^2 := by field_simp
      _ ≤ (18*(D+Q:ℕ)/y)/(Real.sin (Real.pi*((d:ℝ)*theta)))^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ hy.le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hhi) (by norm_num)

theorem vaughan_correction_rational_block (U V D N q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q) (hN : N ≤ q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let A := (4*Real.log 2)*y/(D+1:ℕ)
    let C := 18*(D+q:ℕ)/y
    ‖∑ j ∈ Finset.range N,
      (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticCutoff V ArithmeticFunction.vonMangoldt) (D+j+1):ℝ):ℂ)*
      expSum (fun m => ((etaTwo ((m:ℝ)/(y/(D+j+1:ℕ)))):ℂ))
        (((D+j+1:ℕ):ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      Real.log (D+q:ℕ)*(2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C))) := by
  dsimp only
  let A := (4*Real.log 2)*y/(D+1:ℕ)
  let C := 18*(D+q:ℕ)/y
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDq : (1:ℝ) ≤ (D+q:ℕ) := by exact_mod_cast (show 1 ≤ D+q by omega)
  have hlog : 0 ≤ Real.log (D+q:ℕ) := Real.log_nonneg hDq
  have hpoint : ∀ j ∈ Finset.range N,
      ‖(((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticCutoff V ArithmeticFunction.vonMangoldt) (D+j+1):ℝ):ℂ)*
        expSum (fun m => ((etaTwo ((m:ℝ)/(y/(D+j+1:ℕ)))):ℂ))
          (((D+j+1:ℕ):ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      Real.log (D+q:ℕ)*HelfgottQuadratic.safeCappedSquare A C
        (Real.pi*theta*((D+1:ℕ)+(j:ℝ))+0) := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    have hdhi : D+j+1 ≤ D+q := by omega
    have hlo : D+1 ≤ D+j+1 := by omega
    have hdp : (0:ℝ) < (D+j+1:ℕ) := by positivity
    have hl : |(arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticCutoff V ArithmeticFunction.vonMangoldt) (D+j+1)| ≤ Real.log (D+q:ℕ) :=
      (vaughan_correction_coefficient_abs_le U V _).trans
        (Real.log_le_log hdp (by exact_mod_cast hdhi))
    have he := etaTwo_variable_scale_cap y theta hy (D+j+1) D q hlo hdhi
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hp : Real.pi*(((D+j+1:ℕ):ℝ)*theta) = Real.pi*theta*((D+1:ℕ)+(j:ℝ))+0 := by push_cast; ring
    rw [hp] at he
    exact mul_le_mul hl he (norm_nonneg _) hlog
  calc
    _ ≤ ∑ j ∈ Finset.range N, Real.log (D+q:ℕ)*HelfgottQuadratic.safeCappedSquare A C
        (Real.pi*theta*((D+1:ℕ)+(j:ℝ))+0) := (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = Real.log (D+q:ℕ)*(∑ j ∈ Finset.range N, HelfgottQuadratic.safeCappedSquare A C
        (Real.pi*theta*((D+1:ℕ)+(j:ℝ))+0)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (HelfgottQuadratic.quadratic_rational_block_int a q N hq haq hN theta beta 0 (D+1:ℕ) A C
        htheta hbeta hA hC) hlog

theorem etaTwo_small_divisor_bound (a : ℤ) (q d : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (hd : 0 < d) (hdq : 2*d ≤ q)
    (y theta beta : ℝ) (hy : 0 < y) (htheta : theta = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖expSum (fun m => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)) ((d:ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      18*(d:ℝ)*(q:ℝ)^2/y := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqR : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hsin := HelfgottQuadratic.rational_small_divisor_sine a q d hq haq hd hdq theta beta htheta hbeta
  have hspos : 0 < |Real.sin (Real.pi*((d:ℝ)*theta))| := (one_div_pos.mpr hqR).trans_le hsin
  have hsne := abs_pos.mp hspos
  have hh := HelfgottQuadratic.etaTwo_expSum_quadratic_cap (y/(d:ℝ)) ((d:ℝ)*theta) (div_pos hy hdR)
  rw [if_neg hsne] at hh
  have hsq : (1/(q:ℝ))^2 ≤ (Real.sin (Real.pi*((d:ℝ)*theta)))^2 := by
    have hh := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 1/(q:ℝ)) hsin
    simpa [pow_two] using hh
  calc
    _ ≤ 18/((y/(d:ℝ))*(Real.sin (Real.pi*((d:ℝ)*theta)))^2) := hh.trans (min_le_right _ _)
    _ ≤ 18/((y/(d:ℝ))*(1/(q:ℝ))^2) := div_le_div_of_nonneg_left (by norm_num)
      (by positivity) (mul_le_mul_of_nonneg_left hsq (div_nonneg hy.le hdR.le))
    _ = _ := by field_simp

theorem vaughan_correction_small_divisors (U V N q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q) (hN : 2*N ≤ q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖∑ j ∈ Finset.range N,
      (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticCutoff V ArithmeticFunction.vonMangoldt) (j+1):ℝ):ℂ)*
      expSum (fun m => ((etaTwo ((m:ℝ)/(y/(j+1:ℕ)))):ℂ))
        (((j+1:ℕ):ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      9*(q:ℝ)^2*(N:ℝ)*(N+1:ℕ)*Real.log (q:ℝ)/y := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlq : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg hq1
  have hpoint : ∀ j ∈ Finset.range N,
      ‖(((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticCutoff V ArithmeticFunction.vonMangoldt) (j+1):ℝ):ℂ)*
      expSum (fun m => ((etaTwo ((m:ℝ)/(y/(j+1:ℕ)))):ℂ))
        (((j+1:ℕ):ℝ)*theta:AddCircle (1:ℝ))‖ ≤
      Real.log (q:ℝ)*(18*(j+1:ℕ)*(q:ℝ)^2/y) := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    have hdq : 2*(j+1) ≤ q := by omega
    have hl := (vaughan_correction_coefficient_abs_le U V (j+1)).trans
      (Real.log_le_log (by positivity) (show ((j+1:ℕ):ℝ) ≤ q by exact_mod_cast (show j+1 ≤ q by omega)))
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul hl (etaTwo_small_divisor_bound a q (j+1) hq haq (by omega) hdq y theta beta hy htheta hbeta)
      (norm_nonneg _) hlq
  have hsum : (∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)) = (N:ℝ)*(N+1:ℕ)/2 := by
    clear hN hpoint
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      ring
  calc
    _ ≤ ∑ j ∈ Finset.range N, Real.log (q:ℝ)*(18*(j+1:ℕ)*(q:ℝ)^2/y) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ = (Real.log (q:ℝ)*18*(q:ℝ)^2/y)*(∑ j ∈ Finset.range N, ((j+1:ℕ):ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [hsum]; ring

theorem correction_block_envelope_le (D q : ℕ) (y : ℝ) (hy : 0 < y) (hD : q ≤ 2*(D+1)) :
    let A := (4*Real.log 2)*y/(D+1:ℕ)
    let C := 18*(D+q:ℕ)/y
    2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) ≤
      12*y/(D+1:ℕ)+30*(q:ℝ) := by
  dsimp only
  have hd : (0:ℝ) < (D+1:ℕ) := by positivity
  have hlog : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hratio : (D+q:ℕ)/(D+1:ℕ) ≤ (3:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    have hh : (q:ℝ) ≤ 2*(D+1:ℕ) := by exact_mod_cast hD
    push_cast at hh ⊢
    linarith
  have hproduct : ((4*Real.log 2)*y/(D+1:ℕ))*(18*(D+q:ℕ)/y) ≤ 216 := by
    calc
      _ = 72*Real.log 2*((D+q:ℕ)/(D+1:ℕ)) := by field_simp; ring
      _ ≤ 72*1*3 := mul_le_mul (mul_le_mul_of_nonneg_left hlog (by norm_num)) hratio
        (by positivity) (by norm_num)
      _ = _ := by norm_num
  have hroot : Real.sqrt (((4*Real.log 2)*y/(D+1:ℕ))*(18*(D+q:ℕ)/y)) ≤ 15 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num,by linarith⟩
  have hA : (4*Real.log 2)*y/(D+1:ℕ) ≤ 4*y/(D+1:ℕ) := by gcongr; linarith
  have hmin := min_le_right (2*(18*(D+q:ℕ)/y)*(q:ℝ)^2)
    ((4*Real.log 2)*y/(D+1:ℕ)+2*(q:ℝ)*Real.sqrt (((4*Real.log 2)*y/(D+1:ℕ))*(18*(D+q:ℕ)/y)))
  have hscaled := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(q:ℝ) by positivity)
  rw [show 12*y/(D+1:ℕ) = 3*(4*y/(D+1:ℕ)) by ring]
  linarith

end Helfgott

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
namespace Helfgott

noncomputable def correctionTerm (U V : ℕ) (y theta : ℝ) (j : ℕ) : ℂ :=
  (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
    arithmeticCutoff V ArithmeticFunction.vonMangoldt) (j+1):ℝ):ℂ)*
  expSum (fun m => ((etaTwo ((m:ℝ)/(y/(j+1:ℕ)))):ℂ)) (((j+1:ℕ):ℝ)*theta:AddCircle (1:ℝ))

theorem correctionTerm_block (U V D N q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q) (hN : N ≤ q)
    (hD : q ≤ 2*(D+1)) (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖∑ j ∈ range N, correctionTerm U V y theta (D+j)‖ ≤
      Real.log (D+q:ℕ)*(12*y/(D+1:ℕ)+30*(q:ℝ)) := by
  have hh := vaughan_correction_rational_block U V D N q a y theta beta hy hq haq hN htheta hbeta
  apply hh.trans
  apply mul_le_mul_of_nonneg_left (correction_block_envelope_le D q y hy hD)
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ D+q by omega))

theorem correctionTerm_tail (U V B q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q) (hB : q/2 ≤ B)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖∑ j ∈ range (B-q/2), correctionTerm U V y theta (q/2+j)‖ ≤
      Real.log (B+q:ℕ)*(24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ)) := by
  let K := q/2
  let L := B-K
  let J := L/q+1
  have hqN : 0 < q := by omega
  have hqR : (0:ℝ) < q := by exact_mod_cast hqN
  have hK : q ≤ 2*(K+1) := by dsimp [K]; omega
  have hKL : K+L = B := Nat.add_sub_of_le hB
  have hBQ : (1:ℝ) ≤ (B+q:ℕ) := by exact_mod_cast (show 1 ≤ B+q by omega)
  have hlog : 0 ≤ Real.log (B+q:ℕ) := Real.log_nonneg hBQ
  have hJq : J*q ≤ B+q := by
    have hh := Nat.div_mul_le_self L q
    dsimp [J]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have hJ : J ≤ B+q := (Nat.le_mul_of_pos_right J hqN).trans hJq
  have hJ0 : (0:ℝ) < J := by dsimp [J]; positivity
  have hpoint : ∀ k ∈ range J,
      ‖∑ j ∈ range (min q (L-k*q)), correctionTerm U V y theta (K+(k*q+j))‖ ≤
      Real.log (B+q:ℕ)*(24*y/(q:ℝ)*(1/(k+1:ℕ))+30*(q:ℝ)) := by
    intro k hk
    have hkJ : k ≤ L/q := by have := mem_range.mp hk; dsimp [J] at this; omega
    have hkL : k*q ≤ L := (Nat.mul_le_mul_right q hkJ).trans (Nat.div_mul_le_self L q)
    have hD : q ≤ 2*(K+k*q+1) := by omega
    have hDlog : Real.log (K+k*q+q:ℕ) ≤ Real.log (B+q:ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show K+k*q+q ≤ B+q by omega))
    have hden : (q:ℝ)*(k+1:ℕ) ≤ 2*(K+k*q+1:ℕ) := by
      have hh : (q:ℝ) ≤ 2*(K+1:ℕ) := by exact_mod_cast hK
      push_cast at hh ⊢
      nlinarith [Nat.cast_nonneg (α:=ℝ) k]
    have hfrac : 12*y/(K+k*q+1:ℕ) ≤ 24*y/(q:ℝ)*(1/(k+1:ℕ)) := by
      have hdenp : (0:ℝ) < (K+k*q+1:ℕ) := by positivity
      have hkp : (0:ℝ) < (k+1:ℕ) := by positivity
      rw [show 24*y/(q:ℝ)*(1/(k+1:ℕ)) = 24*y/((q:ℝ)*(k+1:ℕ)) by ring]
      apply (div_le_div_iff₀ hdenp (mul_pos hqR hkp)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 12*y by positivity)]
    have hh := correctionTerm_block U V (K+k*q) (min q (L-k*q)) q a y theta beta hy hq haq
      (min_le_left _ _) hD htheta hbeta
    have hnonneg : 0 ≤ 12*y/(K+k*q+1:ℕ)+30*(q:ℝ) := by positivity
    calc
      _ = ‖∑ j ∈ range (min q (L-k*q)), correctionTerm U V y theta (K+k*q+j)‖ := by simp only [Nat.add_assoc]
      _ ≤ Real.log (K+k*q+q:ℕ)*(12*y/(K+k*q+1:ℕ)+30*(q:ℝ)) := hh
      _ ≤ Real.log (B+q:ℕ)*(24*y/(q:ℝ)*(1/(k+1:ℕ))+30*(q:ℝ)) :=
        mul_le_mul hDlog (add_le_add hfrac le_rfl) hnonneg hlog
  have hharm : (∑ k ∈ range J, (1/(k+1:ℕ):ℝ)) ≤ (1+Real.log (B+q:ℕ):ℝ) := by
    have heq : (∑ k ∈ range J, (1/(k+1:ℕ):ℝ)) = (harmonic J:ℝ) := by
      simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    rw [heq]
    exact (harmonic_le_one_add_log J).trans
      (add_le_add le_rfl (Real.log_le_log hJ0 (by exact_mod_cast hJ)))
  have hcount : 30*(q:ℝ)*(J:ℝ) ≤ 30*(B+q:ℕ) := by
    have hh : (J:ℝ)*(q:ℝ) ≤ (B+q:ℕ) := by exact_mod_cast hJq
    nlinarith
  change ‖∑ j ∈ range L, correctionTerm U V y theta (K+j)‖ ≤ _
  rw [HelfgottQuadratic.sum_range_partition_blocks _ L q hqN]
  calc
    _ ≤ ∑ k ∈ range J, Real.log (B+q:ℕ)*(24*y/(q:ℝ)*(1/(k+1:ℕ))+30*(q:ℝ)) :=
      (norm_sum_le _ _).trans (sum_le_sum hpoint)
    _ = Real.log (B+q:ℕ)*(24*y/(q:ℝ)*(∑ k ∈ range J, (1/(k+1:ℕ):ℝ))+30*(q:ℝ)*(J:ℝ)) := by
      rw [← mul_sum,sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hharm (by positivity)) hcount) hlog

theorem correctionTerm_prefix (U V B q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    ‖∑ j ∈ range B, correctionTerm U V y theta j‖ ≤
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+
        24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ)) := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqR : (0:ℝ) < q := by linarith
  have hBQ : (1:ℝ) ≤ (B+q:ℕ) := by exact_mod_cast (show 1 ≤ B+q by omega)
  have hlog : 0 ≤ Real.log (B+q:ℕ) := Real.log_nonneg hBQ
  have hlogq : Real.log (q:ℝ) ≤ Real.log (B+q:ℕ) :=
    Real.log_le_log hqR (by exact_mod_cast (show q ≤ B+q by omega))
  have hhead : ∀ N : ℕ, 2*N ≤ q →
      ‖∑ j ∈ range N, correctionTerm U V y theta j‖ ≤ Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y) := by
    intro N hN
    have hNq : (N:ℝ) ≤ q := by exact_mod_cast (show N ≤ q by omega)
    have hN1q : ((N+1:ℕ):ℝ) ≤ q := by exact_mod_cast (show N+1 ≤ q by omega)
    have hh := vaughan_correction_small_divisors U V N q a y theta beta hy hq haq hN htheta hbeta
    apply hh.trans
    calc
      _ ≤ 9*(q:ℝ)^2*(q:ℝ)*(q:ℝ)*Real.log (B+q:ℕ)/y := by gcongr
      _ = _ := by ring
  have hrest : 0 ≤ 24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ) := by positivity
  by_cases hB : B ≤ q/2
  · have hh := hhead B (by omega)
    have hr := mul_nonneg hlog hrest
    nlinarith
  · have hKB : q/2 ≤ B := by omega
    have hsum : (∑ j ∈ range B, correctionTerm U V y theta j) =
        (∑ j ∈ range (q/2), correctionTerm U V y theta j)+
        (∑ j ∈ range (B-q/2), correctionTerm U V y theta (q/2+j)) := by
      conv_lhs => rw [← Nat.add_sub_of_le hKB]
      rw [sum_range_add]
    rw [hsum]
    have hh := hhead (q/2) (by omega)
    have ht := correctionTerm_tail U V B q a y theta beta hy hq haq hKB htheta hbeta
    have hn := norm_add_le (∑ j ∈ range (q/2), correctionTerm U V y theta j)
      (∑ j ∈ range (B-q/2), correctionTerm U V y theta (q/2+j))
    nlinarith

theorem vaughan_correction_sum_eq_prefix (U V : ℕ) (y theta : ℝ) (hy : 0 < y) :
    expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ)) =
      ∑ j ∈ range (min (U*V) ⌊y⌋₊), correctionTerm U V y theta j := by
  rw [vaughan_correction_expSum U V y hy]
  have hscale : ∀ d ∈ Icc 1 (min (U*V) ⌊y⌋₊),
      (∑ m ∈ Icc 1 ⌊y/(d:ℝ)⌋₊, ((etaTwo (((d*m:ℕ):ℝ)/y)):ℂ)*
        fourier ((d*m:ℕ):ℤ) (theta:AddCircle (1:ℝ))) =
      expSum (fun m => ((etaTwo ((m:ℝ)/(y/(d:ℝ)))):ℂ)) ((d:ℝ)*theta:AddCircle (1:ℝ)) := by
    intro d hd
    exact etaTwo_product_expSum d (by have := (mem_Icc.mp hd).1; omega) y theta hy
  have heq := sum_congr rfl (fun d hd => congrArg
    (fun z:ℂ => (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticCutoff V ArithmeticFunction.vonMangoldt) d):ℂ)*z) (hscale d hd))
  rw [heq,← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  apply sum_congr rfl
  intro j hj
  simp only [correctionTerm,Nat.add_comm 1 j]

theorem vaughan_correction_rational_upper (U V q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let B := min (U*V) ⌊y⌋₊
    ‖expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+
        24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ)) := by
  rw [vaughan_correction_sum_eq_prefix U V y theta hy]
  exact correctionTerm_prefix U V _ q a y theta beta hy hq haq htheta hbeta

end Helfgott

end

open Helfgott
theorem solution (U V q : ℕ) (a : ℤ) (y theta beta : ℝ)
    (hy : 0 < y) (hq : 2 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (htheta : theta = (a:ℝ)/(q:ℝ)+beta) (hbeta : |beta| ≤ 1/(q:ℝ)^2) :
    let B := min (U*V) ⌊y⌋₊
    ‖expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n:ℝ)/y):ℝ):ℂ)) (theta:AddCircle (1:ℝ))‖ ≤
      Real.log (B+q:ℕ)*(9*(q:ℝ)^4/y+
        24*y/(q:ℝ)*(1+Real.log (B+q:ℕ))+30*(B+q:ℕ)) := by
  exact Helfgott.vaughan_correction_rational_upper U V q a y theta beta hy hq haq htheta hbeta
