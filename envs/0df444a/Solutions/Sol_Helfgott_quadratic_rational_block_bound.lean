-- Prove2me | solution 1 for Helfgott.quadratic_rational_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T17:36:56.21705+00:00
-- url     : https://prove2.me/submissions/6ecb0a86-05a0-4ca0-885f-c974f1c2e068

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

open scoped BigOperators
theorem solution (a : ℤ) (q N : ℕ) (hq : 2 ≤ q)
    (haq : Nat.Coprime a.natAbs q) (hN : N ≤ q) (alpha beta theta M A C : ℝ)
    (halpha : alpha = (a:ℝ)/(q:ℝ)+beta)
    (hbeta : |beta| ≤ 1/(q:ℝ)^2) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ j ∈ Finset.range N,
      if Real.sin (Real.pi*alpha*(M+(j:ℝ))+theta) = 0 then A
      else min A (C/(Real.sin (Real.pi*alpha*(M+(j:ℝ))+theta))^2)) ≤
      2*A+min (2*C*(q:ℝ)^2) (A+2*(q:ℝ)*Real.sqrt (A*C)) := by
  exact HelfgottQuadratic.quadratic_rational_block_int a q N hq haq hN alpha beta theta M A C halpha hbeta hA hC
