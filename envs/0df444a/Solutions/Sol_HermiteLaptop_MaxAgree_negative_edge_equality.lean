-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.negative_edge_equality
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T14:16:25.272697+00:00
-- url     : https://prove2.me/submissions/d8f92075-64f0-4ef0-b1e5-a1f9b52bdc36

import Definitions.Def_HermiteLaptop_MaxAgree_Mixture

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal
namespace HermiteLaptop.MaxAgree

private def strictCell {k : ℕ} (i : Fin k) : Set (Fin k → ℝ) :=
  {x | ∀ j, j ≠ i → x j < x i}

private lemma strictCell_meas {k : ℕ} (i : Fin k) : MeasurableSet (strictCell i) := by
  simp only [strictCell, ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

private lemma strictCell_disj {k : ℕ} : Pairwise (Disjoint on (@strictCell k)) := by
  intro i j hij
  exact Set.disjoint_left.2 fun x hi hj => (hi j hij.symm).not_gt (hj i hij)

private lemma strictCell_spoke {k : ℕ} {p : Fin k} {x : Fin k → ℝ} (hp : x ∈ strictCell p) :
    spokeIndex x = p.val := by
  classical
  have hpmax (q : Fin k) : x q ≤ x p := by
    rcases eq_or_ne q p with rfl | h
    · exact le_rfl
    · exact (hp q h).le
  unfold spokeIndex
  cases h : (List.finRange k).find? (fun p => decide (∀ q, x q ≤ x p)) with
  | none =>
    have hno := List.find?_eq_none.mp h p (List.mem_finRange p)
    simp [hpmax] at hno
  | some q =>
    have hq : ∀ j, x j ≤ x q := by
      simpa only [decide_eq_true_eq] using List.find?_some (p := fun p => decide (∀ j, x j ≤ x p)) h
    have heq : q = p := by
      by_contra hne
      exact (hp q hne).not_ge (hq p)
    simp [heq]

private lemma gaussPi_injective_ae (k : ℕ) : ∀ᵐ x ∂(gaussPi k), Injective x := by
  have : IsProbabilityMeasure (gaussPi k) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let g := gaussianReal 0 1
  let : NullSingletonClass g := nullSingletonClass_gaussianReal one_ne_zero
  let : IsProbabilityMeasure g := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  have ind : iIndepFun (fun (i : Fin k) (x : Fin k → ℝ) => x i) (gaussPi k) :=
    iIndepFun_pi (μ := fun _ => g) (X := fun _ => id) (fun _ => aemeasurable_id)
  have law (i : Fin k) : HasLaw (fun x : Fin k → ℝ => x i) g (gaussPi k) :=
    (measurePreserving_eval (fun _ : Fin k => g) i).hasLaw
  have h (i j : Fin k) : ∀ᵐ x ∂(gaussPi k), i ≠ j → x i ≠ x j := by
    by_cases h : i = j
    · simp [h]
    have pair := (ind.indepFun h).hasLaw_prod (law i) (law j)
    have d : ∀ᵐ z : ℝ × ℝ ∂g.prod g, z.1 ≠ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).2
      exact ae_of_all _ fun x => (g.ae_ne x).mono fun y hy => Ne.symm hy
    have hp : Measurable (fun z : ℝ × ℝ => z.1 ≠ z.2) :=
      measurableSet_setOfPred.1 ((measurableSet_eq_fun measurable_fst measurable_snd).compl)
    simpa [h] using (pair.ae_iff hp).2 d
  filter_upwards [ae_all_iff.2 (fun i => ae_all_iff.2 (h i))] with x hx i j hij
  exact by_contra fun hne => hx i j hne hij

private lemma strictCell_exists {k : ℕ} (hk : 0 < k) {x : Fin k → ℝ} (hx : Injective x) :
    ∃ i, x ∈ strictCell i := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨i, fun j hji => lt_of_le_of_ne (hi j (Finset.mem_univ _)) (fun h => hji (hx h))⟩

private lemma strictCell_same_mass {k : ℕ} (i j : Fin k) :
    (gaussPi k).real (strictCell i) = (gaussPi k).real (strictCell j) := by
  classical
  let e := Equiv.swap i j
  let F := MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e
  have hh : HasLaw F (gaussPi k) (gaussPi k) :=
    (measurePreserving_piCongrLeft (fun _ : Fin k => gaussianReal 0 1) e).hasLaw
  have hf (x : Fin k → ℝ) (q : Fin k) : F x (e q) = x q :=
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k => ℝ) e x q
  have he : e i = j := Equiv.swap_apply_left _ _
  have hs : {x : Fin k → ℝ | F x ∈ strictCell j} = strictCell i := by
    ext x
    change (∀ q, q ≠ j → F x q < F x j) ↔ ∀ q, q ≠ i → x q < x i
    rw [← he]
    constructor
    · intro hx q h
      simpa only [hf] using hx (e q) (fun heq => h (e.injective heq))
    · intro hx q h
      obtain ⟨r, rfl⟩ := e.surjective q
      simpa only [hf] using hx r (fun heq => h (congrArg e heq))
  rw [← hs]
  exact hh.measureReal_eq (strictCell_meas j)

private lemma strictCell_mass {k : ℕ} (i : Fin k) :
    (gaussPi k).real (strictCell i) = 1 / k := by
  have : IsProbabilityMeasure (gaussPi k) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  have hu : (⋃ j : Fin k, strictCell j) =ᵐ[gaussPi k] univ := by
    filter_upwards [gaussPi_injective_ae k] with x hx
    apply propext
    change x ∈ (⋃ j : Fin k, strictCell j) ↔ x ∈ univ
    simpa only [mem_iUnion, mem_univ, iff_true] using strictCell_exists (Nat.zero_lt_of_lt i.isLt) hx
  have hs := measureReal_iUnion_fintype (μ := gaussPi k) (@strictCell_disj k) strictCell_meas
  rw [measureReal_congr hu, probReal_univ] at hs
  simp_rw [fun j => strictCell_same_mass j i] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  exact (eq_div_iff (by exact_mod_cast ((Nat.zero_lt_of_lt i.isLt).ne'))).2 (by linarith [mul_comm ((k : ℕ) : ℝ) ((gaussPi k).real (strictCell i))])

private theorem collisionProb_zero_of_pos (k : ℕ) (hk : 0 < k) :
    collisionProb k 0 = 1 / (k : ℝ) := by
  classical
  have : IsProbabilityMeasure (gaussPi k) := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let A := fun i : Fin k => strictCell i ×ˢ strictCell i
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    exact Set.disjoint_left.2 fun z hi hj => Set.disjoint_left.1 (strictCell_disj hij) hi.1 hj.1
  have hm (i : Fin k) : MeasurableSet (A i) := (strictCell_meas i).prod (strictCell_meas i)
  have hE : {z : (Fin k → ℝ) × (Fin k → ℝ) | spokeIndex z.1 = spokeIndex z.2} =ᵐ[(gaussPi k).prod (gaussPi k)] ⋃ i, A i := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (gaussPi_injective_ae k),
      Measure.quasiMeasurePreserving_snd.ae (gaussPi_injective_ae k)] with z h₁ h₂
    obtain ⟨i, hi⟩ := strictCell_exists hk h₁
    obtain ⟨j, hj⟩ := strictCell_exists hk h₂
    apply propext
    change (spokeIndex z.1 = spokeIndex z.2) ↔ z ∈ ⋃ i, A i
    rw [strictCell_spoke hi, strictCell_spoke hj]
    simp only [mem_iUnion]
    constructor
    · intro he
      have hij : i = j := Fin.ext he
      exact ⟨i, hi, hij ▸ hj⟩
    · rintro ⟨l, hl, hr⟩
      exact (strictCell_spoke hi).symm.trans ((strictCell_spoke hl).trans ((strictCell_spoke hr).symm.trans (strictCell_spoke hj)))
  have hpartner (x y : Fin k → ℝ) : corrPartner 0 x y = y := by
    ext q
    simp [corrPartner]
  unfold collisionProb
  simp_rw [hpartner]
  change ((gaussPi k).prod (gaussPi k)).real _ = _
  rw [measureReal_congr hE, measureReal_iUnion_fintype hd hm]
  simp only [A, measureReal_prod_prod, strictCell_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

end HermiteLaptop.MaxAgree

open HermiteLaptop.MaxAgree

private lemma sum_four_five (μ : Mixture) (h4 : μ.lam 4 = 0.364)
    (h5 : μ.lam 5 = 0.636) (f : ℕ → ℝ) :
    (∑' k, μ.lam k * f k) = 0.364 * f 4 + 0.636 * f 5 := by
  classical
  have hoff (k : ℕ) (hk : k ∉ ({4, 5} : Finset ℕ)) : μ.lam k = 0 := by
    have h := sum_le_hasSum (insert k ({4, 5} : Finset ℕ)) (fun i _ => μ.lam_nonneg i) μ.lam_sum
    rw [Finset.sum_insert hk] at h
    norm_num [Finset.sum_insert, h4, h5] at h
    linarith [μ.lam_nonneg k]
  rw [tsum_eq_sum (s := ({4, 5} : Finset ℕ)) (fun k hk => by simp [hoff k hk])]
  norm_num [Finset.sum_insert, h4, h5]


theorem solution (μ : Mixture) (h4 : μ.lam 4 = 0.364) (h5 : μ.lam 5 = 0.636) :
    1 - μ.collision 0 = 1 - (0.364 * collisionProb 4 0 + 0.636 * collisionProb 5 0) ∧
    0.364 * collisionProb 4 0 + 0.636 * collisionProb 5 0 = 0.364 / 4 + 0.636 / 5 ∧
    (1 : ℝ) - (0.364 / 4 + 0.636 / 5) = 0.7818 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [Mixture.collision, sum_four_five μ h4 h5]
  · rw [collisionProb_zero_of_pos 4 (by decide), collisionProb_zero_of_pos 5 (by decide)]
    norm_num
