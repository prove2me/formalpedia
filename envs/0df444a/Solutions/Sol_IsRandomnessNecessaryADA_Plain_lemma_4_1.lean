-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T17:16:32.998014+00:00
-- url     : https://prove2.me/submissions/7439d6c0-1d44-4cf4-86d9-8613eb4dbbc6

import Definitions.Def_IsRandomnessNecessaryADA_Plain_ConditionalCube
import Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P44_maximal_coupling
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Tables
import Theorems.Thm_IsRandomnessNecessaryADA_Plain_lemma_1_5

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

open scoped Classical in
theorem disint {T U : Type} [Fintype T] [Fintype U] (π : PMF (T × U)) :
    ∃ κ : T → PMF U, (π.map Prod.fst).bind (fun x => (κ x).map (Prod.mk x)) = π := by
  classical
  obtain ⟨⟨t0, u0⟩, _⟩ := π.support_nonempty
  set μ := π.map Prod.fst with hμ
  have hmu : ∀ x, μ x = ∑ u, π (x, u) := by
    intro x
    rw [hμ, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have hk : ∀ x, ∃ p : PMF U, μ x ≠ 0 → ∀ u, p u = π (x, u) / μ x := by
    intro x
    by_cases h : μ x = 0
    · exact ⟨PMF.pure u0, fun h' => absurd h h'⟩
    · refine ⟨PMF.ofFintype (fun u => π (x, u) / μ x) ?_, fun _ u => PMF.ofFintype_apply _ _⟩
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hmu]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _)
  choose κ hκ using hk
  refine ⟨κ, ?_⟩
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · by_cases h : μ a = 0
    · have : π (a, b) = 0 := by
        have h2 := hmu a
        rw [h] at h2
        exact (Finset.sum_eq_zero_iff.1 h2.symm) b (Finset.mem_univ _)
      rw [this, h, zero_mul]
    · rw [PMF.map_apply (Prod.mk a) (κ a), tsum_fintype, Finset.sum_eq_single b]
      · simp only [if_true]
        rw [hκ a h b, ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)]
      · intro u _ hu; simp [hu.symm]
      · simp
  · intro x _ hx
    rw [PMF.map_apply (Prod.mk x) (κ x), tsum_fintype]
    simp [Ne.symm hx]
  · simp


theorem bind_snd {T : Type} [Fintype T] (π : PMF (T × T)) (κ : T → PMF T)
    (hκ : (π.map Prod.fst).bind (fun x => (κ x).map (Prod.mk x)) = π) :
    (π.map Prod.fst).bind κ = π.map Prod.snd := by
  conv_rhs => rw [← hκ]
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp]
  exact (PMF.map_id (κ x)).symm

theorem glue {T : Type} [Fintype T] : ∀ (L : ℕ) (μ : Fin (L + 1) → PMF T)
    (π : Fin L → PMF (T × T)), (∀ t, (π t).map Prod.fst = μ t.castSucc) →
    (∀ t, (π t).map Prod.snd = μ t.succ) →
    ∃ J : PMF (Fin (L + 1) → T), (∀ j, J.map (fun Q => Q j) = μ j) ∧
      ∀ t : Fin L, J.map (fun Q => (Q t.castSucc, Q t.succ)) = π t := by
  intro L
  induction L with
  | zero =>
    intro μ π _ _
    refine ⟨(μ 0).map (fun x _ => x), ?_, fun t => t.elim0⟩
    intro j
    have : j = 0 := Fin.ext (by have := j.2; simp at this ⊢)
    subst this
    rw [PMF.map_comp]
    exact PMF.map_id _
  | succ L ih =>
    intro μ π h1 h2
    obtain ⟨J', hJ'1, hJ'2⟩ := ih (fun j => μ j.castSucc) (fun t => π t.castSucc)
      (fun t => h1 t.castSucc) (fun t => h2 t.castSucc)
    obtain ⟨κ, hκ⟩ := disint (π (Fin.last L))
    have hlast1 : (π (Fin.last L)).map Prod.fst = J'.map (fun Q => Q (Fin.last L)) := by
      rw [hJ'1, h1]
    have hbind : J'.bind (fun q => κ (q (Fin.last L))) = μ (Fin.last L).succ := by
      show J'.bind (κ ∘ fun q => q (Fin.last L)) = _
      rw [← PMF.bind_map, ← hlast1, bind_snd _ _ hκ, h2]
    refine ⟨J'.bind (fun q => (κ (q (Fin.last L))).map (fun x => Fin.snoc (α := fun _ => T) q x)),
      ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [PMF.map_bind]
        have : ∀ q : Fin (L + 1) → T, ((κ (q (Fin.last L))).map
            (fun x => Fin.snoc (α := fun _ => T) q x)).map (fun Q => Q (Fin.last (L + 1))) =
            κ (q (Fin.last L)) := by
          intro q
          rw [PMF.map_comp]
          simp only [Function.comp_def, Fin.snoc_last]
          exact PMF.map_id _
        exact (congrArg J'.bind (funext this)).trans hbind
      · rw [PMF.map_bind]
        have : ∀ q : Fin (L + 1) → T, ((κ (q (Fin.last L))).map
            (fun x => Fin.snoc (α := fun _ => T) q x)).map (fun Q => Q j'.castSucc) =
            PMF.pure (q j') := by
          intro q
          rw [PMF.map_comp]
          simp only [Function.comp_def, Fin.snoc_castSucc]
          exact PMF.map_const _ _
        exact (congrArg J'.bind (funext this)).trans
          ((PMF.bind_pure_comp (fun q : Fin (L + 1) → T => q j') J').trans (hJ'1 j'))
    · intro t
      refine Fin.lastCases ?_ (fun t' => ?_) t
      · rw [PMF.map_bind]
        have : ∀ q : Fin (L + 1) → T, ((κ (q (Fin.last L))).map
            (fun x => Fin.snoc (α := fun _ => T) q x)).map
              (fun Q => (Q (Fin.last L).castSucc, Q (Fin.last L).succ)) =
            (κ (q (Fin.last L))).map (Prod.mk (q (Fin.last L))) := by
          intro q
          rw [PMF.map_comp]
          simp only [Function.comp_def, Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
        refine (congrArg J'.bind (funext this)).trans ?_
        show J'.bind ((fun y => (κ y).map (Prod.mk y)) ∘ fun q => q (Fin.last L)) = _
        rw [← PMF.bind_map, ← hlast1]
        exact hκ
      · rw [PMF.map_bind]
        have : ∀ q : Fin (L + 1) → T, ((κ (q (Fin.last L))).map
            (fun x => Fin.snoc (α := fun _ => T) q x)).map
              (fun Q => (Q t'.castSucc.castSucc, Q t'.castSucc.succ)) =
            PMF.pure (q t'.castSucc, q t'.succ) := by
          intro q
          rw [PMF.map_comp]
          simp only [Function.comp_def, Fin.succ_castSucc, Fin.snoc_castSucc]
          exact PMF.map_const _ _
        exact (congrArg J'.bind (funext this)).trans
          ((PMF.bind_pure_comp (fun q : Fin (L + 1) → T => (q t'.castSucc, q t'.succ)) J').trans (hJ'2 t'))


theorem bind_pair_apply {T U : Type} [Fintype T] [Fintype U] (μ : PMF T) (κ : T → PMF U)
    (a : T) (b : U) :
    (μ.bind (fun x => (κ x).map (Prod.mk x))) (a, b) = μ a * κ a b := by
  classical
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [PMF.map_apply (Prod.mk a) (κ a), tsum_fintype, Finset.sum_eq_single b]
    · simp
    · intro u _ hu; simp [hu.symm]
    · simp
  · intro x _ hx
    rw [PMF.map_apply (Prod.mk x) (κ x), tsum_fintype]
    simp [Ne.symm hx]
  · simp

theorem bind_snd' {T U : Type} [Fintype T] [Fintype U] (π : PMF (T × U)) (κ : T → PMF U)
    (hκ : (π.map Prod.fst).bind (fun x => (κ x).map (Prod.mk x)) = π) :
    (π.map Prod.fst).bind κ = π.map Prod.snd := by
  conv_rhs => rw [← hκ]
  rw [PMF.map_bind]
  congr 1
  funext x
  rw [PMF.map_comp]
  exact (PMF.map_id (κ x)).symm

/-- the disintegration of μ along f -/
theorem disint_fun {T P : Type} [Fintype T] [Fintype P] (μ : PMF T) (f : T → P) :
    ∃ κ : P → PMF T, (μ.map f).bind κ = μ ∧
      ∀ y, (μ.map f) y ≠ 0 → ∀ x, κ y x ≠ 0 → f x = y := by
  obtain ⟨κ, hκ⟩ := disint (μ.map (fun x => (f x, x)))
  have hf : (μ.map (fun x => (f x, x))).map Prod.fst = μ.map f := by
    rw [PMF.map_comp]; rfl
  rw [hf] at hκ
  refine ⟨κ, ?_, ?_⟩
  · have := bind_snd' _ _ (by rw [hf]; exact hκ)
    rw [hf] at this
    rw [this, PMF.map_comp]
    exact PMF.map_id μ
  · intro y hy x hx
    by_contra hne
    have h1 := bind_pair_apply (μ.map f) κ y x
    rw [hκ] at h1
    have h2 : (μ.map (fun x => (f x, x))) (y, x) = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      refine Finset.sum_eq_zero (fun x' _ => ?_)
      by_cases h : (y, x) = (f x', x')
      · exfalso; apply hne
        have := (Prod.mk.inj h)
        rw [this.2, this.1]
      · simp [h]
    rw [h2] at h1
    exact (mul_ne_zero hy hx) h1.symm


open QAlgorithms.Papers.Independent.Bridge50.P44 in
theorem pmf_max_coupling {P : Type} [Fintype P] (ν ν' : PMF P) :
    ∃ j : PMF (P × P), j.map Prod.fst = ν ∧ j.map Prod.snd = ν' ∧
      (j.toOuterMeasure {yy | yy.1 ≠ yy.2}).toReal ≤
        discreteTV (fun y => (ν y).toReal) (fun y => (ν' y).toReal) := by
  classical
  have hlaw : ∀ ρ : PMF P, IsDiscreteLaw (fun y => (ρ y).toReal) := by
    intro ρ
    refine ⟨fun y => ENNReal.toReal_nonneg, Summable.of_finite, ?_⟩
    rw [tsum_fintype, ← ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top _ _)]
    have : ∑ y, ρ y = 1 := by have := ρ.tsum_coe; rwa [tsum_fintype] at this
    rw [this]; simp
  obtain ⟨j0, ⟨⟨hj0, hjs, hj1⟩, hrow, hcol⟩, hge⟩ :=
    maximal_coupling (fun y => (ν y).toReal) (fun y => (ν' y).toReal) (hlaw ν) (hlaw ν')
  have hsum1 : ∑ yy, j0 yy = 1 := by rw [tsum_fintype] at hj1; exact hj1
  have hOne : ∑ yy, ENNReal.ofReal (j0 yy) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun yy _ => hj0 yy), hsum1]; simp
  let j : PMF (P × P) := PMF.ofFintype (fun yy => ENNReal.ofReal (j0 yy)) hOne
  have hjapp : ∀ yy, j yy = ENNReal.ofReal (j0 yy) := fun _ => rfl
  refine ⟨j, ?_, ?_, ?_⟩
  · ext y
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single y]
    · simp only [hjapp, if_true]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hj0 _)]
      have := hrow y
      rw [tsum_fintype] at this
      rw [this]
      exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  · ext y
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
    have : ∀ a : P, (∑ w : P, if y = w then ENNReal.ofReal (j0 (a, w)) else 0) =
        ENNReal.ofReal (j0 (a, y)) := by
      intro a
      simp [Finset.sum_ite_eq]
    simp only [hjapp, this]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hj0 _)]
    have := hcol y
    rw [tsum_fintype] at this
    rw [this]
    exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)
  · rw [PMF.toOuterMeasure_apply_fintype, ENNReal.toReal_sum (fun yy _ =>
      ne_top_of_le_ne_top (PMF.apply_ne_top j yy) (Set.indicator_le_self _ _ yy))]
    have e1 : ∀ yy : P × P, (({yy : P × P | yy.1 ≠ yy.2} : Set (P × P)).indicator j yy).toReal =
        if yy.1 ≠ yy.2 then j0 yy else 0 := by
      intro yy
      by_cases h : yy.1 ≠ yy.2
      · simp [Set.indicator_of_mem (show yy ∈ {yy : P × P | yy.1 ≠ yy.2} from h), h, hjapp,
          ENNReal.toReal_ofReal (hj0 yy)]
      · simp [Set.indicator_of_notMem (show yy ∉ {yy : P × P | yy.1 ≠ yy.2} from h), h]
    simp only [e1]
    have e2 : ∑ yy : P × P, (if yy.1 ≠ yy.2 then j0 yy else 0) =
        1 - ∑ z : P, j0 (z, z) := by
      have : ∑ yy : P × P, (if yy.1 ≠ yy.2 then j0 yy else 0) +
          ∑ yy : P × P, (if yy.1 = yy.2 then j0 yy else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← hsum1]
        refine Finset.sum_congr rfl (fun yy _ => ?_)
        by_cases h : yy.1 = yy.2 <;> simp [h]
      have e3 : ∑ yy : P × P, (if yy.1 = yy.2 then j0 yy else 0) = ∑ z : P, j0 (z, z) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      linarith
    rw [e2]
    have := hge
    rw [tsum_fintype] at this
    linarith


theorem outer_le_one {α : Type} (ρ : PMF α) (s : Set α) : ρ.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply]
  calc ∑' x, s.indicator ρ x ≤ ∑' x, ρ x := ENNReal.tsum_le_tsum (fun x => Set.indicator_le_self _ _ x)
    _ = 1 := ρ.tsum_coe

theorem pair_coupling {T P : Type} [Fintype T] [Fintype P] (μ μ' : PMF T) (f : T → P) :
    ∃ π : PMF (T × T), π.map Prod.fst = μ ∧ π.map Prod.snd = μ' ∧
      (π.toOuterMeasure {p | f p.1 ≠ f p.2}).toReal ≤ pmfTV (μ.map f) (μ'.map f) := by
  classical
  obtain ⟨κ, hκ, hκs⟩ := disint_fun μ f
  obtain ⟨κ', hκ', hκs'⟩ := disint_fun μ' f
  obtain ⟨j, hj1, hj2, hjm⟩ := pmf_max_coupling (μ.map f) (μ'.map f)
  let G : P × P → PMF (T × T) := fun yy =>
    (κ yy.1).bind (fun x => (κ' yy.2).map (Prod.mk x))
  refine ⟨j.bind G, ?_, ?_, ?_⟩
  · rw [PMF.map_bind]
    have : ∀ yy : P × P, (G yy).map Prod.fst = κ yy.1 := by
      intro yy
      simp only [G]
      rw [PMF.map_bind]
      have : ∀ x : T, ((κ' yy.2).map (Prod.mk x)).map Prod.fst = PMF.pure x := by
        intro x
        rw [PMF.map_comp]
        exact PMF.map_const _ _
      simp_rw [this]
      exact PMF.bind_pure _
    refine (congrArg j.bind (funext this)).trans ?_
    show j.bind (κ ∘ Prod.fst) = μ
    rw [← PMF.bind_map, hj1, hκ]
  · rw [PMF.map_bind]
    have : ∀ yy : P × P, (G yy).map Prod.snd = κ' yy.2 := by
      intro yy
      simp only [G]
      rw [PMF.map_bind]
      have : ∀ x : T, ((κ' yy.2).map (Prod.mk x)).map Prod.snd = κ' yy.2 := by
        intro x
        rw [PMF.map_comp]
        exact PMF.map_id _
      simp_rw [this]
      exact PMF.bind_const _ _
    refine (congrArg j.bind (funext this)).trans ?_
    show j.bind (κ' ∘ Prod.snd) = μ'
    rw [← PMF.bind_map, hj2, hκ']
  · have hle : (j.bind G).toOuterMeasure {p | f p.1 ≠ f p.2} ≤
        j.toOuterMeasure {yy | yy.1 ≠ yy.2} := by
      rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
      refine ENNReal.tsum_le_tsum (fun yy => ?_)
      by_cases hF : yy ∈ {yy : P × P | yy.1 ≠ yy.2}
      · rw [Set.indicator_of_mem hF]
        calc j yy * (G yy).toOuterMeasure {p | f p.1 ≠ f p.2} ≤ j yy * 1 :=
              mul_le_mul' le_rfl (outer_le_one _ _)
          _ = j yy := mul_one _
      · rw [Set.indicator_of_notMem hF]
        by_cases hj : j yy = 0
        · rw [hj, zero_mul]
        · have hyy : yy.1 = yy.2 := by simpa using hF
          have hsup : yy ∈ j.support := (PMF.mem_support_iff _ _).2 hj
          have hν : (μ.map f) yy.1 ≠ 0 := by
            rw [← hj1, ← PMF.mem_support_iff, PMF.support_map]
            exact ⟨yy, hsup, rfl⟩
          have hν' : (μ'.map f) yy.2 ≠ 0 := by
            rw [← hj2, ← PMF.mem_support_iff, PMF.support_map]
            exact ⟨yy, hsup, rfl⟩
          have h0 : (G yy).toOuterMeasure {p | f p.1 ≠ f p.2} = 0 := by
            rw [PMF.toOuterMeasure_apply_eq_zero_iff]
            rw [Set.disjoint_left]
            intro p hp hpE
            simp only [G, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hp
            obtain ⟨x, hx, x', hx', rfl⟩ := hp
            have h1 : f x = yy.1 := hκs _ hν x ((PMF.mem_support_iff _ _).1 hx)
            have h2 : f x' = yy.2 := hκs' _ hν' x' ((PMF.mem_support_iff _ _).1 hx')
            apply hpE
            show f x = f x'
            rw [h1, h2, hyy]
          rw [h0, mul_zero]
    have hne : j.toOuterMeasure {yy | yy.1 ≠ yy.2} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _)
    exact (ENNReal.toReal_mono hne hle).trans hjm


theorem chain_coupling {T : Type} [Fintype T] (L : ℕ) (μ : Fin (L + 1) → PMF T)
    (agree : Fin L → T → T → Prop) (ε : Fin L → ℝ)
    (hpair : ∀ t : Fin L, ∃ π : PMF (T × T), π.map Prod.fst = μ t.castSucc ∧
      π.map Prod.snd = μ t.succ ∧ (π.toOuterMeasure {p | ¬ agree t p.1 p.2}).toReal ≤ ε t) :
    ∃ J : PMF (Fin (L + 1) → T), (∀ j, J.map (fun Q => Q j) = μ j) ∧
      1 - ∑ t, ε t ≤ (J.toOuterMeasure {Q | ∀ t, agree t (Q t.castSucc) (Q t.succ)}).toReal := by
  classical
  choose π h1 h2 h3 using hpair
  obtain ⟨J, hJ1, hJ2⟩ := glue L μ π h1 h2
  refine ⟨J, hJ1, ?_⟩
  set S : Set (Fin (L + 1) → T) := {Q | ∀ t, agree t (Q t.castSucc) (Q t.succ)} with hS
  have hsum : ∑ Q, J Q = 1 := by have := J.tsum_coe; rwa [tsum_fintype] at this
  have hne : ∀ s : Set (Fin (L + 1) → T), J.toOuterMeasure s ≠ ⊤ := fun s =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _)
  have hcompl : J.toOuterMeasure S + J.toOuterMeasure Sᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype,
      ← Finset.sum_add_distrib, ← hsum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    exact congrFun (Set.indicator_self_add_compl S J) Q
  have hfail : J.toOuterMeasure Sᶜ ≤ ∑ t : Fin L, (π t).toOuterMeasure {p | ¬ agree t p.1 p.2} := by
    have hbad : ∀ t : Fin L, (π t).toOuterMeasure {p | ¬ agree t p.1 p.2} =
        J.toOuterMeasure {Q | ¬ agree t (Q t.castSucc) (Q t.succ)} := by
      intro t
      rw [← hJ2 t, PMF.toOuterMeasure_map_apply]; rfl
    simp only [hbad]
    rw [PMF.toOuterMeasure_apply_fintype]
    simp only [PMF.toOuterMeasure_apply_fintype]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun Q _ => ?_)
    by_cases hQ : Q ∈ Sᶜ
    · rw [Set.indicator_of_mem hQ]
      have : ∃ t, ¬ agree t (Q t.castSucc) (Q t.succ) := by
        by_contra hcon; push Not at hcon; exact hQ hcon
      obtain ⟨t, ht⟩ := this
      refine le_trans ?_ (Finset.single_le_sum (f := fun t : Fin L =>
        {Q' : Fin (L + 1) → T | ¬ agree t (Q' t.castSucc) (Q' t.succ)}.indicator J Q)
        (fun _ _ => zero_le) (Finset.mem_univ t))
      rw [Set.indicator_of_mem (show Q ∈ {Q' : Fin (L + 1) → T | ¬ agree t (Q' t.castSucc) (Q' t.succ)} from ht)]
    · rw [Set.indicator_of_notMem hQ]; exact zero_le
  have hr1 : (J.toOuterMeasure S).toReal + (J.toOuterMeasure Sᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (hne _) (hne _), hcompl]; simp
  have hr2 : (J.toOuterMeasure Sᶜ).toReal ≤ ∑ t : Fin L, ε t := by
    have hfne : (∑ t : Fin L, (π t).toOuterMeasure {p | ¬ agree t p.1 p.2}) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 (fun t _ => ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _))
    refine (ENNReal.toReal_mono hfne hfail).trans ?_
    rw [ENNReal.toReal_sum (fun t _ => ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _))]
    exact Finset.sum_le_sum (fun t _ => h3 t)
  linarith

end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

open IsRandomnessNecessaryADA.Plain

theorem umap_apply {A B : Type} [Fintype A] [Nonempty A] [DecidableEq B] (H : A → B) (y : B) :
    (((PMF.uniformOfFintype A).map H) y).toReal =
      (1 / (Fintype.card A : ℝ)) * ∑ a : A, if H a = y then (1 : ℝ) else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : H x = y
    · simp [h, eq_comm]
    · simp [h, Ne.symm h]
  · intro x _
    split_ifs <;> simp

theorem pmfTV_uniform_map {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [DecidableEq B]
    (H H' : A → B) :
    pmfTV ((PMF.uniformOfFintype A).map H) ((PMF.uniformOfFintype A).map H') =
      (1 / 2 : ℝ) * ∑ y : B, |(1 / (Fintype.card A : ℝ)) *
        ∑ a : A, ((if H a = y then (1 : ℝ) else 0) - (if H' a = y then (1 : ℝ) else 0))| := by
  unfold pmfTV QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
  rw [tsum_fintype]
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  beta_reduce
  rw [umap_apply, umap_apply, Finset.sum_sub_distrib, ← mul_sub]


section Decomp

variable {N M : ℕ} (i : Fin N)

abbrev Rest (N M : ℕ) (i : Fin N) := {x : Fin N × Fin M // x.1 ≠ i} → Bool

def splitEquiv : Table N M ≃ (Fin M → Bool) × Rest N M i where
  toFun Q := (fun u => Q (i, u), fun x => Q x.1)
  invFun p := fun x => if hx : x.1 = i then p.1 x.2 else p.2 ⟨x, hx⟩
  left_inv Q := by
    funext x
    by_cases hx : x.1 = i
    · simp only [hx, dif_pos]; rw [← hx]
    · simp [hx]
  right_inv p := by
    refine Prod.ext (funext fun u => ?_) (funext fun x => ?_)
    · simp
    · show (if hx : x.1.1 = i then p.1 x.1.2 else p.2 ⟨x.1, hx⟩) = p.2 x
      rw [dif_neg x.2]

theorem splitEquiv_symm_apply (p : (Fin M → Bool) × Rest N M i) (x : Fin N × Fin M) :
    (splitEquiv i).symm p x = if hx : x.1 = i then p.1 x.2 else p.2 ⟨x, hx⟩ := rfl

theorem update_symm (ξ : Fin M → Bool) (z : Rest N M i) (u : Fin M) (b : Bool) :
    Function.update ((splitEquiv i).symm (ξ, z)) (i, u) b =
      (splitEquiv i).symm (Function.update ξ u b, z) := by
  funext x
  by_cases hx : x = (i, u)
  · subst hx; simp [splitEquiv_symm_apply]
  · by_cases h1 : x.1 = i
    · have : x.2 ≠ u := fun h => hx (Prod.ext h1 h)
      simp [splitEquiv_symm_apply, Function.update_of_ne hx, h1, Function.update_of_ne this]
    · simp [splitEquiv_symm_apply, Function.update_of_ne hx, h1]

end Decomp


section Decomp2

variable {N M : ℕ} (i : Fin N)

def C0 (r : Locations N M) (v : BooleanQuery (Fin N)) (Q : Table N M) : Table N M :=
  fun x => if x.1 ≠ i ∧ x.2 = r x.1 then v x.1 else Q x

theorem cb (r : Locations N M) (v : BooleanQuery (Fin N)) (u : Fin M) (b : Bool) (Q : Table N M) :
    completeTable (Function.update r i u) (Function.update v i b) Q =
      Function.update (C0 i r v Q) (i, u) b := by
  funext ⟨j, w⟩
  unfold completeTable C0
  by_cases hj : j = i
  · subst hj
    by_cases hw : w = u
    · subst hw; simp
    · have h1 : ((j, w) : Fin N × Fin M) ≠ (j, u) := fun h => hw (Prod.mk.inj h).2
      simp [Function.update_of_ne h1, hw]
  · have h1 : ((j, w) : Fin N × Fin M) ≠ (i, u) := fun h => hj (Prod.mk.inj h).1
    simp [Function.update_of_ne h1, Function.update_of_ne hj, hj]

def phi (r : Locations N M) (v : BooleanQuery (Fin N)) (z : Rest N M i) : Rest N M i :=
  fun x => if x.1.2 = r x.1.1 then v x.1.1 else z x

theorem C0_symm (r : Locations N M) (v : BooleanQuery (Fin N)) (ξ : Fin M → Bool)
    (z : Rest N M i) :
    C0 i r v ((splitEquiv i).symm (ξ, z)) = (splitEquiv i).symm (ξ, phi i r v z) := by
  funext x
  by_cases hx : x.1 = i
  · simp [C0, splitEquiv_symm_apply, hx]
  · simp [C0, splitEquiv_symm_apply, hx, phi]

theorem rp_indep {n : ℕ} (m : Mechanism (Fin N × Fin M) n) (r : Locations N M)
    (h : List (Table N M)) (u : Fin M) :
    responseProfile m (Function.update r i u) h i = responseProfile m r h i := by
  funext q s
  unfold responseProfile
  have : rowSample (Function.update r i u) (fun t => (s t).val) = rowSample r (fun t => (s t).val) := by
    funext t
    simp [rowSample, Function.update_of_ne (s t).2]
  simp only [this]

end Decomp2


theorem pmfTV_map_equiv {A B : Type} [Fintype A] [Fintype B] (p q : PMF A) (e : A ≃ B) :
    pmfTV (p.map e) (q.map e) = pmfTV p q := by
  classical
  have hmap : ∀ (ρ : PMF A) (a : A), (ρ.map e) (e a) = ρ a := by
    intro ρ a
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [e.injective.ne hb.symm]
    · simp
  unfold pmfTV QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
  rw [tsum_fintype, tsum_fintype, ← e.sum_comp]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [hmap]

theorem avg_abs {Y Z : Type} [Fintype Y] [Fintype Z] (c R : ℝ) (hc : 0 < c) (hR : 0 < R)
    (A : Z → Y → ℝ) :
    (1 / 2 : ℝ) * ∑ y, |1 / (c * R) * ∑ z, A z y| ≤
      (1 / R) * ∑ z, (1 / 2 : ℝ) * ∑ y, |1 / c * A z y| := by
  have step : ∀ y, |1 / (c * R) * ∑ z, A z y| ≤ (1 / R) * ∑ z, |1 / c * A z y| := by
    intro y
    have : 1 / (c * R) * ∑ z, A z y = (1 / R) * ∑ z, (1 / c * A z y) := by
      rw [← Finset.mul_sum, ← mul_assoc, one_div_mul_one_div, mul_comm R c]
    rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / R)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  calc (1 / 2 : ℝ) * ∑ y, |1 / (c * R) * ∑ z, A z y|
      ≤ (1 / 2 : ℝ) * ∑ y, (1 / R) * ∑ z, |1 / c * A z y| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => step y)) (by norm_num)
    _ = (1 / R) * ∑ z, (1 / 2 : ℝ) * ∑ y, |1 / c * A z y| := by
        rw [← Finset.mul_sum, Finset.sum_comm, mul_left_comm, Finset.mul_sum]

theorem tv_bound {N M n : ℕ} [NeZero M] (m : Mechanism (Fin N × Fin M) n) (r : Locations N M)
    (h : List (Table N M)) (i : Fin N) (v : BooleanQuery (Fin N)) :
    (∑ u : Fin M, pmfTV
      ((completionLaw (Function.update r i u) (Function.update v i false)).map
        (responseProfile m (Function.update r i u) h i))
      ((completionLaw (Function.update r i u) (Function.update v i true)).map
        (responseProfile m (Function.update r i u) h i))) ≤
      M * Real.sqrt (2 * (N : ℝ) ^ n / M) := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set F := responseProfile m r h i with hF
  simp only [rp_indep]
  rw [← hF]
  set d := Fintype.card (Fin n → {j : Fin N // j ≠ i}) with hd
  let enc : ((Fin n → {j : Fin N // j ≠ i}) → Bool) ≃ (Fin d → Bool) :=
    Equiv.arrowCongr (Fintype.equivFin _) (Equiv.refl Bool)
  let g : Rest N M i → (Fin M → Bool) → (Fin d → Bool) := fun z ξ =>
    enc (F ((splitEquiv i).symm (ξ, phi i r v z)))
  have hmain : ∀ u : Fin M, pmfTV ((completionLaw (Function.update r i u) (Function.update v i false)).map F)
      ((completionLaw (Function.update r i u) (Function.update v i true)).map F) ≤
      (1 / (Fintype.card (Rest N M i) : ℝ)) * ∑ z : Rest N M i,
        pmfTV ((coordinateLaw u false).map (g z)) ((coordinateLaw u true).map (g z)) := by
    intro u
    rw [← pmfTV_map_equiv _ _ enc]
    simp only [PMF.map_comp]
    have e1 : ∀ b : Bool, (completionLaw (Function.update r i u) (Function.update v i b)).map (enc ∘ F) =
        (PMF.uniformOfFintype (Table N M)).map
          (fun Q => enc (F (Function.update (C0 i r v Q) (i, u) b))) := by
      intro b
      unfold completionLaw tableLaw
      rw [PMF.map_comp]
      congr 1
      funext Q
      simp [Function.comp, cb]
    have e3 : ∀ z : Rest N M i, pmfTV ((coordinateLaw u false).map (g z)) ((coordinateLaw u true).map (g z)) =
        (1 / 2 : ℝ) * ∑ y : Fin d → Bool, |(1 / (Fintype.card (Fin M → Bool) : ℝ)) *
          ∑ ξ : Fin M → Bool, ((if g z (Function.update ξ u false) = y then (1 : ℝ) else 0) -
            (if g z (Function.update ξ u true) = y then (1 : ℝ) else 0))| := by
      intro z
      unfold coordinateLaw
      rw [PMF.map_comp, PMF.map_comp]
      exact pmfTV_uniform_map _ _
    simp only [e3]
    rw [e1 false, e1 true, pmfTV_uniform_map]
    have hcard : (Fintype.card (Table N M) : ℝ) =
        (Fintype.card (Fin M → Bool) : ℝ) * Fintype.card (Rest N M i) := by
      rw [Fintype.card_congr (splitEquiv i)]
      simp
    have hsumQ : ∀ (y : Fin d → Bool), ∑ Q : Table N M,
        ((if enc (F (Function.update (C0 i r v Q) (i, u) false)) = y then (1 : ℝ) else 0) -
          (if enc (F (Function.update (C0 i r v Q) (i, u) true)) = y then (1 : ℝ) else 0)) =
        ∑ z : Rest N M i, ∑ ξ : Fin M → Bool,
          ((if g z (Function.update ξ u false) = y then (1 : ℝ) else 0) -
            (if g z (Function.update ξ u true) = y then (1 : ℝ) else 0)) := by
      intro y
      rw [← Equiv.sum_comp (splitEquiv i).symm, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun ξ _ => ?_))
      simp only [C0_symm, update_symm, g]
    simp only [hsumQ, hcard]
    have hcpos : (0 : ℝ) < Fintype.card (Fin M → Bool) := by exact_mod_cast Fintype.card_pos
    have hRpos : (0 : ℝ) < Fintype.card (Rest N M i) := by exact_mod_cast Fintype.card_pos
    exact avg_abs _ _ hcpos hRpos (fun z y => ∑ ξ : Fin M → Bool,
      ((if g z (Function.update ξ u false) = y then (1 : ℝ) else 0) -
        (if g z (Function.update ξ u true) = y then (1 : ℝ) else 0)))
  have hsum : ∀ z : Rest N M i, (∑ u : Fin M, pmfTV ((coordinateLaw u false).map (g z))
      ((coordinateLaw u true).map (g z))) ≤ M * Real.sqrt (2 * (d : ℝ) / M) := by
    intro z
    have := lemma_1_5 M d hM (g z)
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMr] at this
    linarith
  have hdN : (d : ℝ) ≤ (N : ℝ) ^ n := by
    have : d = (Fintype.card {j : Fin N // j ≠ i}) ^ n := by
      simp [hd]
    rw [this]
    have h2 : Fintype.card {j : Fin N // j ≠ i} ≤ N := by
      simpa using Fintype.card_subtype_le (fun j : Fin N => j ≠ i)
    exact_mod_cast Nat.pow_le_pow_left h2 n
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : Real.sqrt (2 * (d : ℝ) / M) ≤ Real.sqrt (2 * (N : ℝ) ^ n / M) :=
    Real.sqrt_le_sqrt (by gcongr)
  have hRpos : (0 : ℝ) < Fintype.card (Rest N M i) := by exact_mod_cast Fintype.card_pos
  calc (∑ u : Fin M, pmfTV ((completionLaw (Function.update r i u) (Function.update v i false)).map F)
      ((completionLaw (Function.update r i u) (Function.update v i true)).map F))
      ≤ ∑ u : Fin M, ((1 / (Fintype.card (Rest N M i) : ℝ)) * ∑ z : Rest N M i,
        pmfTV ((coordinateLaw u false).map (g z)) ((coordinateLaw u true).map (g z))) :=
        Finset.sum_le_sum (fun u _ => hmain u)
    _ = (1 / (Fintype.card (Rest N M i) : ℝ)) * ∑ z : Rest N M i, ∑ u : Fin M,
        pmfTV ((coordinateLaw u false).map (g z)) ((coordinateLaw u true).map (g z)) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (1 / (Fintype.card (Rest N M i) : ℝ)) * ∑ z : Rest N M i,
        ((M : ℝ) * Real.sqrt (2 * (N : ℝ) ^ n / M)) := by
        gcongr with z hz
        exact (hsum z).trans (by gcongr)
    _ = M * Real.sqrt (2 * (N : ℝ) ^ n / M) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L41

open IsRandomnessNecessaryADA.Plain

theorem sum_loc_update {N M : ℕ} (i : Fin N) (G : (Fin N → Fin M) → ℝ) :
    (M : ℝ) * ∑ r, G r = ∑ r, ∑ u : Fin M, G (Function.update r i u) := by
  classical
  let e := Equiv.funSplitAt i (Fin M)
  have hupd : ∀ (a u : Fin M) (b : {j // j ≠ i} → Fin M),
      Function.update (e.symm (a, b)) i u = e.symm (u, b) := by
    intro a u b
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.funSplitAt]
    · simp [e, Equiv.funSplitAt, Function.update_apply, hj]
  rw [← e.symm.sum_comp G, ← e.symm.sum_comp (fun r => ∑ u : Fin M, G (Function.update r i u))]
  simp only [hupd, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_comm]


theorem tp_step {N : ℕ} (p : ThresholdPath N) (t : Fin p.length) :
    thresholdPattern p t.castSucc (p.change t) = false ∧
      thresholdPattern p t.succ =
        Function.update (thresholdPattern p t.castSucc) (p.change t) true := by
  classical
  have hcomm := p.complement
  constructor
  · unfold thresholdPattern
    simp only [decide_eq_false_iff_not, not_or, not_exists, not_and, Fin.coe_castSucc]
    refine ⟨fun hmem => (hcomm _).1 hmem t rfl, fun t' ht' hc => ?_⟩
    have : t' = t := p.change.injective hc
    subst this
    exact lt_irrefl _ ht'
  · funext j
    by_cases hj : j = p.change t
    · subst hj
      rw [Function.update_self]
      unfold thresholdPattern
      simp only [decide_eq_true_eq]
      exact Or.inr ⟨t, by simp, rfl⟩
    · rw [Function.update_of_ne hj]
      unfold thresholdPattern
      congr 1
      apply propext
      constructor
      · rintro (h | ⟨t', ht', hc⟩)
        · exact Or.inl h
        · right
          refine ⟨t', ?_, hc⟩
          have : t'.val ≠ t.val := fun h => hj (hc ▸ congrArg p.change (Fin.ext h) ▸ rfl)
          simp at ht' ⊢
          omega
      · rintro (h | ⟨t', ht', hc⟩)
        · exact Or.inl h
        · right
          refine ⟨t', ?_, hc⟩
          simp at ht' ⊢
          omega

theorem sum_update_gen {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι) (G : (ι → Bool) → ℝ)
    (b : Bool) :
    ∑ x : ι → Bool, G (Function.update x u b) =
      2 * ∑ x : ι → Bool, if x u = b then G x else 0 := by
  classical
  let e : (ι → Bool) ≃ (ι → Bool) :=
    { toFun := fun x => Function.update x u (!x u)
      invFun := fun x => Function.update x u (!x u)
      left_inv := fun x => by ext i; by_cases h : i = u <;> simp [h]
      right_inv := fun x => by ext i; by_cases h : i = u <;> simp [h] }
  have hsplit : ∑ x : ι → Bool, G (Function.update x u b) =
      ∑ x : ι → Bool, (if x u = b then G (Function.update x u b) else 0) +
      ∑ x : ι → Bool, (if x u = b then 0 else G (Function.update x u b)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  have hp1 : ∑ x : ι → Bool, (if x u = b then G (Function.update x u b) else 0) =
      ∑ x : ι → Bool, if x u = b then G x else 0 := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : x u = b
    · simp only [h, if_true]; rw [← h, Function.update_eq_self]
    · simp [h]
  have hp2 : ∑ x : ι → Bool, (if x u = b then 0 else G (Function.update x u b)) =
      ∑ x : ι → Bool, if x u = b then G x else 0 := by
    rw [← e.sum_comp (fun z : ι → Bool => if z u = b then G z else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : (e x) u = !x u := by simp [e]
    by_cases h : x u = b
    · simp [this, h]
    · have hb : (!x u) = b := by cases hx : x u <;> cases b <;> simp_all
      simp [this, h, hb, e]
  rw [hsplit, hp1, hp2]; ring

theorem count_false (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ∑ v : Fin N → Bool, (if v i = false then (1 : ℝ) else 0) = (2 : ℝ) ^ (N - 1) := by
  have h := sum_update_gen i (fun _ => (1 : ℝ)) false
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hN' : N = (N - 1) + 1 := by omega
  have : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    conv_lhs => rw [hN']
    rw [pow_succ]; ring
  have h2 : (↑(2 ^ N) : ℝ) = (2 : ℝ) ^ N := by push_cast; rfl
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

end IsRandomnessNecessaryADA.Plain.Dev.L41
end

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

theorem Dev.L41.pmfTV_nonneg {Z : Type} (p q : PMF Z) : 0 ≤ pmfTV p q := by
  unfold pmfTV QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
  exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => abs_nonneg _)

open scoped Classical in
theorem chk_lemma_4_1 (N M n : ℕ) (hN : 0 < N) [NeZero M]
    (m : Mechanism (Fin N × Fin M) n) (h : List (Table N M))
    (path : Locations N M → ThresholdPath N) :
    ∃ K : (r : Locations N M) → PMF (Fin ((path r).length + 1) → Table N M),
      (∀ r j, (K r).map (fun Q => Q j) = completionLaw r (thresholdPattern (path r) j)) ∧
      1 - (N : ℝ) * (2 : ℝ) ^ (N - 1) * Real.sqrt (2 * (N : ℝ) ^ n / M) ≤
        probability
          ((PMF.uniformOfFintype (Locations N M)).bind (fun r =>
            (K r).map (fun Q => decide (profilesAgree m r h (path r) Q))))
          {true} := by
  classical
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  set s := Real.sqrt (2 * (N : ℝ) ^ n / M) with hs
  let W : Locations N M → Fin N → BooleanQuery (Fin N) → ℝ := fun r i v =>
    pmfTV ((completionLaw r (Function.update v i false)).map (responseProfile m r h i))
      ((completionLaw r (Function.update v i true)).map (responseProfile m r h i))
  let ε : (r : Locations N M) → Fin (path r).length → ℝ := fun r t =>
    pmfTV ((completionLaw r (thresholdPattern (path r) t.castSucc)).map
        (responseProfile m r h ((path r).change t)))
      ((completionLaw r (thresholdPattern (path r) t.succ)).map
        (responseProfile m r h ((path r).change t)))
  have hK : ∀ r, ∃ K : PMF (Fin ((path r).length + 1) → Table N M),
      (∀ j, K.map (fun Q => Q j) = completionLaw r (thresholdPattern (path r) j)) ∧
      1 - ∑ t, ε r t ≤ (K.toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal := by
    intro r
    exact Dev.L41.chain_coupling (path r).length
      (fun j => completionLaw r (thresholdPattern (path r) j))
      (fun t Q Q' => responseProfile m r h ((path r).change t) Q =
        responseProfile m r h ((path r).change t) Q') (ε r)
      (fun t => Dev.L41.pair_coupling _ _ _)
  choose K hK1 hK2 using hK
  refine ⟨K, hK1, ?_⟩
  have hWnn : ∀ r i v, 0 ≤ W r i v := by
    intro r i v
    exact Dev.L41.pmfTV_nonneg _ _
  have hLoc : (0 : ℝ) < Fintype.card (Locations N M) := by exact_mod_cast Fintype.card_pos
  -- per-r reduction
  have hε : ∀ r, ∑ t, ε r t ≤ ∑ i : Fin N, ∑ v : Fin N → Bool,
      (if v i = false then W r i v else 0) := by
    intro r
    set G : Fin N × (Fin N → Bool) → ℝ := fun p => if p.2 p.1 = false then W r p.1 p.2 else 0
      with hG
    have e1 : ∀ t : Fin (path r).length, ε r t =
        G ((path r).change t, thresholdPattern (path r) t.castSucc) := by
      intro t
      obtain ⟨h1, h2⟩ := Dev.L41.tp_step (path r) t
      simp only [hG, h1, if_true]
      show pmfTV _ _ = pmfTV _ _
      rw [h2]
      have : Function.update (thresholdPattern (path r) t.castSucc) ((path r).change t) false =
          thresholdPattern (path r) t.castSucc := by
        funext j
        by_cases hj : j = (path r).change t
        · subst hj; simp [h1]
        · simp [Function.update_of_ne hj]
      rw [this]
    simp only [e1]
    have hinj : Function.Injective (fun t : Fin (path r).length =>
        (((path r).change t, thresholdPattern (path r) t.castSucc) :
          Fin N × (Fin N → Bool))) := by
      intro a b hab
      exact (path r).change.injective (Prod.mk.inj hab).1
    rw [← Finset.sum_image (f := G) (g := fun t : Fin (path r).length =>
        (((path r).change t, thresholdPattern (path r) t.castSucc) :
          Fin N × (Fin N → Bool))) (fun a _ b _ hab => hinj hab)]
    calc ∑ x ∈ Finset.univ.image (fun t : Fin (path r).length =>
          (((path r).change t, thresholdPattern (path r) t.castSucc) : Fin N × (Fin N → Bool))), G x
        ≤ ∑ x : Fin N × (Fin N → Bool), G x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => by
            simp only [hG]; split_ifs
            · exact hWnn _ _ _
            · exact le_rfl)
      _ = _ := by rw [Fintype.sum_prod_type]
  have havg : ∀ i v, ∑ r, W r i v ≤ (Fintype.card (Locations N M) : ℝ) * s := by
    intro i v
    have h1 := Dev.L41.sum_loc_update i (fun r => W r i v)
    have h2 : ∀ r : Locations N M, ∑ u : Fin M, W (Function.update r i u) i v ≤ M * s :=
      fun r => Dev.L41.tv_bound m r h i v
    have h3 : ∑ r : Locations N M, ∑ u : Fin M, W (Function.update r i u) i v ≤
        ∑ r : Locations N M, (M * s) := Finset.sum_le_sum (fun r _ => h2 r)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    have : (M : ℝ) * ∑ r, W r i v ≤ (M : ℝ) * ((Fintype.card (Locations N M) : ℝ) * s) := by
      rw [h1]; linarith
    exact (mul_le_mul_iff_right₀ hMr).1 this
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hbound : ∑ r : Locations N M, ∑ i : Fin N, ∑ v : Fin N → Bool,
      (if v i = false then W r i v else 0) ≤
      (Fintype.card (Locations N M) : ℝ) * ((N : ℝ) * (2 : ℝ) ^ (N - 1) * s) := by
    rw [Finset.sum_comm]
    have e1 : ∀ i : Fin N, ∑ r : Locations N M, ∑ v : Fin N → Bool,
        (if v i = false then W r i v else 0) =
        ∑ v : Fin N → Bool, (if v i = false then ∑ r, W r i v else 0) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs <;> simp
    simp only [e1]
    calc ∑ i : Fin N, ∑ v : Fin N → Bool, (if v i = false then ∑ r, W r i v else 0)
        ≤ ∑ i : Fin N, ∑ v : Fin N → Bool,
            (if v i = false then (Fintype.card (Locations N M) : ℝ) * s else 0) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun v _ => ?_))
          split_ifs
          · exact havg i v
          · exact le_rfl
      _ = ∑ i : Fin N, ((Fintype.card (Locations N M) : ℝ) * s) *
            ∑ v : Fin N → Bool, (if v i = false then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          split_ifs <;> simp
      _ = _ := by
          simp only [Dev.L41.count_false N hN, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the probability
  have hP : probability
      ((PMF.uniformOfFintype (Locations N M)).bind (fun r =>
        (K r).map (fun Q => decide (profilesAgree m r h (path r) Q)))) {true} =
      (1 / (Fintype.card (Locations N M) : ℝ)) * ∑ r : Locations N M,
        ((K r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal := by
    unfold probability
    rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
    have hne : ∀ r : Locations N M, ((PMF.uniformOfFintype (Locations N M)) r *
        ((K r).map (fun Q => decide (profilesAgree m r h (path r) Q))).toOuterMeasure {true}) ≠ ⊤ :=
      fun r => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        (ne_top_of_le_ne_top ENNReal.one_ne_top (Dev.L41.outer_le_one _ _))
    rw [ENNReal.toReal_sum (fun r _ => hne r), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply]
    have hu : ((PMF.uniformOfFintype (Locations N M)) r).toReal =
        1 / (Fintype.card (Locations N M) : ℝ) := by
      simp [PMF.uniformOfFintype_apply]
    rw [hu]
    congr 3
    ext Q
    simp
  rw [hP]
  have hsum : ∑ r : Locations N M, (1 - ∑ t, ε r t) ≤ ∑ r : Locations N M,
      ((K r).toOuterMeasure {Q | profilesAgree m r h (path r) Q}).toReal :=
    Finset.sum_le_sum (fun r _ => hK2 r)
  have hsum2 : ∑ r : Locations N M, (1 - ∑ t, ε r t) ≥
      (Fintype.card (Locations N M) : ℝ) * (1 - (N : ℝ) * (2 : ℝ) ^ (N - 1) * s) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : ∑ r : Locations N M, ∑ t, ε r t ≤ ∑ r : Locations N M, ∑ i : Fin N, ∑ v : Fin N → Bool,
        (if v i = false then W r i v else 0) := Finset.sum_le_sum (fun r _ => hε r)
    nlinarith
  calc 1 - (N : ℝ) * (2 : ℝ) ^ (N - 1) * s
      = (1 / (Fintype.card (Locations N M) : ℝ)) *
          ((Fintype.card (Locations N M) : ℝ) * (1 - (N : ℝ) * (2 : ℝ) ^ (N - 1) * s)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum2.trans hsum) (by positivity)
end IsRandomnessNecessaryADA.Plain
end

theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.chk_lemma_4_1 := @IsRandomnessNecessaryADA.Plain.chk_lemma_4_1
