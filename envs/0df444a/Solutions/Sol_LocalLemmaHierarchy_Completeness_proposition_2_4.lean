-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:18:19.437752+00:00
-- url     : https://prove2.me/submissions/c268cb61-1c8d-4569-a30c-974543dc703b

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
import Theorems.Thm_LocalLemmaHierarchy_Completeness_theorem_2_3

section
set_option autoImplicit false

open scoped ENNReal NNReal Classical

namespace LocalLemmaHierarchy.Completeness.Dev.P24

open MvPolynomial LocalLemmaHierarchy.Completeness

variable {V T : Type}

lemma aeval_cast (p : MvPolynomial T ℝ) (x : T → ℝ) :
    aeval (fun τ => ((x τ : ℝ) : ℂ)) p = ((eval x p : ℝ) : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma coeff_nonneg (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) :
    ∀ (n : ℕ) (U : Finset V), U.card = n → ∀ m, 0 ≤ (Z U).coeff m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hU m
    by_cases hne : U.Nonempty
    · obtain ⟨v, hv⟩ := hne
      classical
      rw [hZ.2.2 U v hv, coeff_add, coeff_sum]
      refine add_nonneg
        (ih _ (by rw [← hU]; exact Finset.card_erase_lt_of_mem hv) _ rfl m)
        (Finset.sum_nonneg fun a _ => ?_)
      rw [mul_assoc, coeff_C_mul, coeff_X_mul']
      have hlt : (U \ R.D v a).card < n := by
        rw [← hU]
        apply Finset.card_lt_card
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro h
        have := h hv
        simp [R.A_subset_D v a (R.self_mem_A v a)] at this
      apply mul_nonneg (R.c_pos v a).le
      split_ifs
      exacts [ih _ hlt _ rfl _, le_rfl]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [hZ.1, coeff_one]
      split_ifs <;> norm_num

lemma eq_one_of_eval_one (p : MvPolynomial T ℝ) (hnn : ∀ m, 0 ≤ p.coeff m)
    (h0 : eval (0 : T → ℝ) p = 1) (h1 : eval (fun _ => (1 : ℝ)) p = 1) : p = 1 := by
  classical
  have e0 : eval (0 : T → ℝ) p = p.coeff 0 := by
    rw [eval_zero]; rfl
  have e1 : eval (fun _ => (1 : ℝ)) p = ∑ d ∈ p.support, p.coeff d := by
    show eval₂ (RingHom.id ℝ) _ p = _
    rw [eval₂_eq]; simp
  have hc0 : p.coeff 0 = 1 := by rw [← e0, h0]
  have hmem : (0 : T →₀ ℕ) ∈ p.support := by
    rw [mem_support_iff, hc0]; norm_num
  rw [← Finset.add_sum_erase _ _ hmem, hc0] at e1
  have hz : ∑ d ∈ p.support.erase 0, p.coeff d = 0 := by linarith [h1]
  rw [h1] at e1
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => hnn d)).1 hz
  ext m
  rw [coeff_one]
  by_cases hm : m = 0
  · subst hm; simp [hc0]
  · have : p.coeff m = 0 := by
      by_cases hs : m ∈ p.support
      · exact this m (Finset.mem_erase.2 ⟨hm, hs⟩)
      · simpa using hs
    rw [this]; simp [Ne.symm hm]

/-- deletion comparison: nonnegativity propagates a step. -/
lemma step_le (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (S : Finset V) (v : V) (hv : v ∈ S) (t : ℝ) (ht : 0 ≤ t)
    (hnn : ∀ W ⊆ S, 0 ≤ negEval Z W (fun _ => t)) :
    negEval Z S (fun _ => t) ≤ negEval Z (S.erase v) (fun _ => t) := by
  classical
  unfold negEval
  rw [hZ.2.2 S v hv]
  simp only [map_add, map_sum, map_mul, eval_C, eval_X]
  have : ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ S),
      R.c v a * -t * eval (fun τ => -t) (Z (S \ R.D v a)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro a _
    have h := hnn (S \ R.D v a) Finset.sdiff_subset
    unfold negEval at h
    have hc := (R.c_pos v a).le
    have : R.c v a * -t ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg this h
  linarith

lemma le_of_subset (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (n : ℕ) (U : Finset V), U.card = n → (∀ W ⊆ U, 0 ≤ negEval Z W (fun _ => t)) →
      ∀ W ⊆ U, negEval Z U (fun _ => t) ≤ negEval Z W (fun _ => t) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hU hnn W hW
    by_cases hWU : W = U
    · subst hWU; exact le_rfl
    · obtain ⟨v, hvU, hvW⟩ : ∃ v ∈ U, v ∉ W := by
        by_contra hcon
        push Not at hcon
        exact hWU (Finset.Subset.antisymm hW hcon)
      have h1 := step_le R Z hZ U v hvU t ht hnn
      have hsub : W ⊆ U.erase v := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hvW (h ▸ hx), hW hx⟩
      have h2 := ih _ (by rw [← hU]; exact Finset.card_erase_lt_of_mem hvU) (U.erase v) rfl
        (fun W' hW' => hnn W' (hW'.trans (Finset.erase_subset _ _))) W hsub
      exact h1.trans h2

lemma cont (Z : Finset V → MvPolynomial T ℝ) (W : Finset V) :
    Continuous fun t : ℝ => negEval Z W (fun _ => t) :=
  (continuous_eval (Z W)).comp (continuous_pi fun _ => continuous_neg)

lemma zf_iff (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (U : Finset V) (t : ℝ≥0) :
    ZeroFreeOn Z U (fun _ => (t : ℝ)) ↔ ∀ W ⊆ U, 0 < negEval Z W (fun _ => (t : ℝ)) := by
  classical
  exact (theorem_2_3 R Z hZ U _ (fun _ => t.2)).1

lemma zf_mono (Z : Finset V → MvPolynomial T ℝ) (U : Finset V) {s t : ℝ≥0} (hst : s ≤ t)
    (h : ZeroFreeOn Z U (fun _ => (t : ℝ))) : ZeroFreeOn Z U (fun _ => (s : ℝ)) :=
  fun z hz => h z (fun τ => (hz τ).trans (by exact_mod_cast hst))

lemma zf_open (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (U : Finset V) (t : ℝ≥0)
    (h : ZeroFreeOn Z U (fun _ => (t : ℝ))) :
    ∃ s : ℝ≥0, t < s ∧ ZeroFreeOn Z U (fun _ => (s : ℝ)) := by
  have h' := (zf_iff R Z hZ U t).1 h
  have hev : ∀ᶠ s in nhds (t : ℝ), ∀ W ∈ U.powerset, 0 < negEval Z W (fun _ => s) := by
    rw [Filter.eventually_all_finset]
    intro W hW
    exact (cont Z W).continuousAt.eventually (lt_mem_nhds (h' W (Finset.mem_powerset.1 hW)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hpos : (0 : ℝ) < ε / 2 := by positivity
  refine ⟨t + (ε / 2).toNNReal, ?_, ?_⟩
  · exact lt_add_of_pos_right _ (Real.toNNReal_pos.2 hpos)
  · rw [zf_iff R Z hZ]
    intro W hW
    refine hball ?_ W (Finset.mem_powerset.2 hW)
    rw [Real.dist_eq, NNReal.coe_add, Real.coe_toNNReal _ hpos.le,
      abs_of_nonneg (by simp; positivity)]
    simp; linarith

lemma zf_zero (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (U : Finset V) :
    ZeroFreeOn Z U (fun _ => ((0 : ℝ≥0) : ℝ)) := by
  intro z hz
  have : z = fun τ => (((0 : T → ℝ) τ : ℝ) : ℂ) := by
    funext τ
    have := hz τ
    simpa using this
  rw [this, aeval_cast, hZ.2.1 U]
  simp

lemma nonneg_at (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ)
    (hZ : IsRepresentationOf R Z) (U : Finset V) (r : ℝ≥0) (hr : 0 < r)
    (hz : ∀ s : ℝ≥0, s < r → ZeroFreeOn Z U (fun _ => (s : ℝ))) :
    ∀ W ⊆ U, 0 ≤ negEval Z W (fun _ => (r : ℝ)) := by
  intro W hW
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hlim := ((cont Z W).tendsto (r : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (r : ℝ)))
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hr'] with s hs
  have := (zf_iff R Z hZ U s.toNNReal).1
    (hz _ (by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]; exact hs.2)) W hW
  rw [Real.coe_toNNReal _ hs.1.le] at this
  exact this.le

end LocalLemmaHierarchy.Completeness.Dev.P24

namespace LocalLemmaHierarchy.Completeness

open Dev.P24 in
theorem chk_proposition_2_4 {V T : Type} (R : PosLocalDeletionRep V T)
    (Z : Finset V → MvPolynomial T ℝ) (hRZ : IsRepresentationOf R Z) (U : Finset V) :
    regionRadius Z U =
        ⨅ (t : ℝ≥0) (_ : 0 < t ∧ negEval Z U (fun _ => (t : ℝ)) = 0), (t : ℝ≥0∞) ∧
    regionRadius Z U =
        ⨅ (z : ℂ) (_ : MvPolynomial.aeval (fun _ : T => z) (Z U) = 0), (‖z‖₊ : ℝ≥0∞) ∧
    (regionRadius Z U = ⊤ ↔ Z U = 1) ∧
    (regionRadius Z U ≠ ⊤ → negEval Z U (fun _ => (regionRadius Z U).toReal) = 0) ∧
    ∀ t : ℝ≥0, (ZeroFreeOn Z U (fun _ => (t : ℝ)) ↔ (t : ℝ≥0∞) < regionRadius Z U) := by
  classical
  have key : ∀ t : ℝ≥0, ZeroFreeOn Z U (fun _ => (t : ℝ)) ↔ (t : ℝ≥0∞) < regionRadius Z U := by
    intro t
    constructor
    · intro ht
      obtain ⟨s, hts, hs⟩ := zf_open R Z hRZ U t ht
      exact lt_of_lt_of_le (by exact_mod_cast hts)
        (le_iSup₂ (f := fun (t : ℝ≥0) (_ : ZeroFreeOn Z U (fun _ => (t : ℝ))) => (t : ℝ≥0∞))
          s hs)
    · intro h
      unfold regionRadius at h
      rw [lt_iSup_iff] at h
      obtain ⟨s, h⟩ := h
      rw [lt_iSup_iff] at h
      obtain ⟨hs, hts⟩ := h
      exact zf_mono Z U (by exact_mod_cast hts.le) hs
  have hpos : 0 < regionRadius Z U := by
    have := (key 0).1 (zf_zero R Z hRZ U)
    simpa using this
  have hroot : regionRadius Z U ≠ ⊤ →
      negEval Z U (fun _ => (regionRadius Z U).toReal) = 0 := by
    intro hne
    have hcoe : ((regionRadius Z U).toNNReal : ℝ≥0∞) = regionRadius Z U :=
      ENNReal.coe_toNNReal hne
    have hrpos : 0 < (regionRadius Z U).toNNReal := by
      rw [← ENNReal.coe_pos, hcoe]; exact hpos
    have hz : ∀ s : ℝ≥0, s < (regionRadius Z U).toNNReal → ZeroFreeOn Z U (fun _ => (s : ℝ)) :=
      fun s hs => (key s).2 (by rw [← hcoe]; exact_mod_cast hs)
    have hnn := nonneg_at R Z hRZ U _ hrpos hz
    have hnot : ¬ ZeroFreeOn Z U (fun _ => (((regionRadius Z U).toNNReal : ℝ≥0) : ℝ)) := by
      intro h
      have := (key _).1 h
      rw [hcoe] at this
      exact lt_irrefl _ this
    rw [zf_iff R Z hRZ] at hnot
    push Not at hnot
    obtain ⟨W, hW, hle⟩ := hnot
    have h0 := le_antisymm hle (hnn W hW)
    have h1 := le_of_subset R Z hRZ _ (NNReal.coe_nonneg _) _ U rfl hnn W hW
    have h2 := hnn U subset_rfl
    exact le_antisymm (h1.trans h0.le) h2
  have hI : regionRadius Z U =
      ⨅ (t : ℝ≥0) (_ : 0 < t ∧ negEval Z U (fun _ => (t : ℝ)) = 0), (t : ℝ≥0∞) := by
    apply le_antisymm
    · refine le_iInf fun t => le_iInf fun ht => ?_
      by_contra hlt
      push Not at hlt
      have hzf := (key t).2 hlt
      have := (zf_iff R Z hRZ U t).1 hzf U subset_rfl
      linarith [ht.2]
    · by_cases hne : regionRadius Z U = ⊤
      · rw [hne]; exact le_top
      · have hcoe : ((regionRadius Z U).toNNReal : ℝ≥0∞) = regionRadius Z U :=
          ENNReal.coe_toNNReal hne
        have hrpos : 0 < (regionRadius Z U).toNNReal := by
          rw [← ENNReal.coe_pos, hcoe]; exact hpos
        calc _ ≤ (((regionRadius Z U).toNNReal : ℝ≥0) : ℝ≥0∞) :=
              iInf₂_le (f := fun (t : ℝ≥0)
                (_ : 0 < t ∧ negEval Z U (fun _ => (t : ℝ)) = 0) => (t : ℝ≥0∞))
                _ ⟨hrpos, by simpa [ENNReal.coe_toNNReal_eq_toReal] using hroot hne⟩
          _ = _ := hcoe
  have hC : regionRadius Z U =
      ⨅ (z : ℂ) (_ : MvPolynomial.aeval (fun _ : T => z) (Z U) = 0), (‖z‖₊ : ℝ≥0∞) := by
    apply le_antisymm
    · refine le_iInf fun z => le_iInf fun hz => ?_
      by_contra hlt
      push Not at hlt
      have hzf := (key ‖z‖₊).2 hlt
      exact hzf (fun _ => z) (fun _ => by simp) hz
    · by_cases hne : regionRadius Z U = ⊤
      · rw [hne]; exact le_top
      · have hcoe : ((regionRadius Z U).toNNReal : ℝ≥0∞) = regionRadius Z U :=
          ENNReal.coe_toNNReal hne
        have hr := hroot hne
        have hz : MvPolynomial.aeval (fun _ : T => (((-((regionRadius Z U).toReal)) : ℝ) : ℂ))
            (Z U) = 0 := by
          have := aeval_cast (Z U) (fun _ => -((regionRadius Z U).toReal))
          rw [this]
          have h : MvPolynomial.eval (fun _ : T => -((regionRadius Z U).toReal)) (Z U) = 0 := hr
          rw [h]; simp
        calc _ ≤ ((‖(((-((regionRadius Z U).toReal)) : ℝ) : ℂ)‖₊ : ℝ≥0) : ℝ≥0∞) :=
              iInf₂_le (f := fun (z : ℂ)
                (_ : MvPolynomial.aeval (fun _ : T => z) (Z U) = 0) => (‖z‖₊ : ℝ≥0∞)) _ hz
          _ = _ := by
              rw [← hcoe]
              congr 1
              ext
              simp [ENNReal.coe_toNNReal_eq_toReal]
  refine ⟨hI, hC, ?_, hroot, key⟩
  constructor
  · intro htop
    by_contra hne
    have hnn := coeff_nonneg R Z hRZ _ U rfl
    -- q is the diagonal univariate polynomial
    set q : Polynomial ℂ := MvPolynomial.aeval (fun _ : T => (Polynomial.X : Polynomial ℂ)) (Z U)
      with hq
    have hev : ∀ z : ℂ, q.eval z = MvPolynomial.aeval (fun _ : T => z) (Z U) := by
      intro z
      rw [hq]
      induction (Z U) using MvPolynomial.induction_on with
      | C a => simp
      | add p r hp hr => simp [hp, hr]
      | mul_X p i hp => simp [hp]
    have hdeg : 0 < q.degree := by
      by_contra hd
      push Not at hd
      rw [Polynomial.eq_C_of_degree_le_zero hd] at hev
      apply hne
      apply eq_one_of_eval_one _ hnn (hRZ.2.1 U)
      have e0 := hev 0
      have e1 := hev 1
      simp only [Polynomial.eval_C] at e0 e1
      have a0 := aeval_cast (Z U) 0
      have a1 := aeval_cast (Z U) (fun _ => 1)
      have : ((MvPolynomial.eval (0 : T → ℝ) (Z U) : ℝ) : ℂ) =
          ((MvPolynomial.eval (fun _ : T => (1 : ℝ)) (Z U) : ℝ) : ℂ) := by
        rw [← a0, ← a1]
        convert (e0.symm.trans e1) using 2 <;> simp
      have := Complex.ofReal_injective this
      rw [← this]; exact hRZ.2.1 U
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    have hz' : MvPolynomial.aeval (fun _ : T => z) (Z U) = 0 := by rw [← hev]; exact hz
    have hzf := (key ‖z‖₊).2 (by rw [htop]; exact ENNReal.coe_lt_top)
    exact hzf (fun _ => z) (fun _ => le_rfl) hz'
  · intro h1
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro t
    have hzf : ZeroFreeOn Z U (fun _ => (t : ℝ)) := by
      intro z _
      rw [h1]; simp
    exact ((key t).1 hzf).le

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_proposition_2_4 := @LocalLemmaHierarchy.Completeness.chk_proposition_2_4
