-- Prove2me | solution 1 for NashPoly.Generic.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:25:31.311276+00:00
-- url     : https://prove2.me/submissions/dba05c0d-c8ef-4cbd-a2a4-14c75a30d343

import Mathlib
import Definitions.Def_NashPoly_Generic_Algorithm

open MvPolynomial Matrix NashPoly.Generic

namespace Sol32Fem

theorem quad_lower {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Θ : Matrix ι ι ℝ) (hΘ : Θ.PosDef) :
    ∃ μ > 0, ∀ v : ι → ℝ, μ * ‖v‖ ^ 2 ≤ v ⬝ᵥ Θ *ᵥ v := by
  have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ Θ *ᵥ v := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i0 1, by simp [Pi.norm_single]⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hpos : 0 < w ⬝ᵥ Θ *ᵥ w := by
    simpa using hΘ.dotProduct_mulVec_pos hw0
  refine ⟨_, hpos, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hnv.ne']
  have := hmin hs
  simp only [Set.mem_ofPred_eq] at this
  have key : (‖v‖⁻¹ • v) ⬝ᵥ Θ *ᵥ (‖v‖⁻¹ • v) = ‖v‖⁻¹ ^ 2 * (v ⬝ᵥ Θ *ᵥ v) := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul]; simp [smul_eq_mul]; ring
  rw [key] at this
  have h2 : 0 < ‖v‖ ^ 2 := by positivity
  calc (w ⬝ᵥ Θ *ᵥ w) * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * (v ⬝ᵥ Θ *ᵥ v)) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this h2.le
    _ = v ⬝ᵥ Θ *ᵥ v := by field_simp

variable {N : ℕ} {n m : Fin N → ℕ}

theorem cont_blk (i : Fin N) : Continuous fun x : Var n → ℝ => blk x i :=
  continuous_pi fun k => continuous_apply _

theorem cont_repl (i : Fin N) (v : Fin (n i) → ℝ) :
    Continuous fun x : Var n → ℝ => repl x i v := by
  refine continuous_pi fun w => ?_
  rcases w with ⟨j, k⟩
  by_cases h : j = i
  · subst h; simp [repl]; exact continuous_const
  · simp only [repl, Function.update_of_ne h]; exact continuous_apply _

theorem cont_evalblk (i : Fin N) (p : MvPolynomial (Fin (n i)) ℝ) :
    Continuous fun x : Var n → ℝ => eval (blk x i) p :=
  (continuous_eval p).comp (cont_blk i)

theorem cont_gradf (P : NEP N n m) (i : Fin N) (k : Fin (n i)) :
    Continuous fun x => P.gradf i x k := continuous_eval _

theorem cont_gradg (P : NEP N n m) (i : Fin N) (j : Fin (m i)) (k : Fin (n i)) :
    Continuous fun x => P.gradg i j x k := cont_evalblk i _

theorem cont_lam (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (i : Fin N) (j : Fin (m i)) : Continuous fun x => P.lam H i x j := by
  unfold NEP.lam
  refine continuous_finsetSum _ fun r _ => (cont_evalblk i _).mul ?_
  rcases r with k | k
  · exact cont_gradf P i k
  · exact continuous_const

theorem closed_feas (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) : IsClosed (P.Feas H K) := by
  unfold NEP.Feas NEP.GSet
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i => isClosed_iInter
    fun v => isClosed_iInter fun _ => isClosed_le (continuous_eval _)
      ((continuous_eval _).comp (cont_repl i v)))
  refine IsClosed.inter (isClosed_iInter fun k => isClosed_eq ?_ continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (cont_evalblk i _) continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((cont_lam P H i j).mul (cont_evalblk i _)) continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (cont_evalblk i _))
    (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (cont_lam P H i j)))))
  exact (cont_gradf P i k).sub (continuous_finsetSum _ fun j _ =>
    (cont_lam P H i j).mul (cont_gradg P i j k))

end Sol32Fem

open Sol32Fem in
theorem Sol32Fem.feas_min {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hΘ : Θ.PosDef)
    (hne : (P.Feas H K).Nonempty) :
    ∃ u ∈ P.Feas H K, IsMinOn (theta Θ) (P.Feas H K) u := by
  classical
  obtain ⟨μ, hμ, hq⟩ := quad_lower Θ hΘ
  have hct : Continuous (theta Θ : (Var n → ℝ) → ℝ) := by
    have : Continuous (xbar1 : (Var n → ℝ) → Option (Var n) → ℝ) := by
      refine continuous_pi fun o => ?_
      cases o with
      | none => exact continuous_const
      | some w => exact continuous_apply w
    unfold theta
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨x0, hx0⟩ := hne
  set S := P.Feas H K ∩ {x | theta Θ x ≤ theta Θ x0} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((closed_feas P H K).inter (isClosed_le hct continuous_const)) ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (theta Θ x0 / μ), fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ ‖xbar1 x‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
      have := norm_le_pi_norm (xbar1 x) (some w)
      simpa [xbar1] using this
    have h2 : μ * ‖xbar1 x‖ ^ 2 ≤ theta Θ x0 := (hq _).trans hx.2
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hμ]
    have h3 : ‖x‖ ^ 2 ≤ ‖xbar1 x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [mul_le_mul_of_nonneg_left h3 hμ.le]
  obtain ⟨u, hu, hmin⟩ := hSc.exists_isMinOn ⟨x0, hx0, show theta Θ x0 ≤ theta Θ x0 from le_refl _⟩ hct.continuousOn
  refine ⟨u, hu.1, fun x hx => ?_⟩
  by_cases h : theta Θ x ≤ theta Θ x0
  · exact hmin ⟨hx, h⟩
  · push Not at h
    show theta Θ u ≤ theta Θ x
    exact (hu.2).trans h.le

namespace Sol32Aux

variable {N : ℕ} {n m : Fin N → ℕ}

theorem gset_feasible (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    {x : Var n → ℝ} (hx : x ∈ P.GSet H) : P.IsFeasible x :=
  fun i => ⟨(hx i).2.1, (hx i).2.2.2.1⟩

section
variable (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) {L : ℕ}
    {K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ)} {u : Fin L → Var n → ℝ}

theorem run_mono (hrun : P.IsRun H Θ L K u) :
    ∀ (s t : Fin (L + 1)), s ≤ t → ∀ i, K s i ⊆ K t i := by
  intro s t
  induction t using Fin.induction with
  | zero =>
    intro hst i
    have : s = 0 := le_antisymm hst (Fin.zero_le _)
    subst this; exact le_rfl
  | succ ℓ ih =>
    intro hst i
    rcases le_or_gt s ℓ.castSucc with h | h
    · obtain ⟨U, hU, -, -⟩ := (hrun.2 ℓ).2.2.2 i
      rw [hU]; exact (ih h i).trans Set.subset_union_left
    · have : s = ℓ.succ := le_antisymm hst (Fin.castSucc_lt_iff_succ_le.mp h)
      subst this; exact le_rfl

theorem not_ne_improve {x : Var n → ℝ} (hfe : P.IsFeasible x) (hne : ¬ P.IsNE x) :
    ∃ i, P.CanImprove i x := by
  by_contra hcon
  push Not at hcon
  apply hne
  refine ⟨hfe, fun i v hv => ?_⟩
  by_contra h
  push Not at h
  exact hcon i ⟨v, hv, h⟩

theorem run_cut (hrun : P.IsRun H Θ L K u) (ℓ : Fin L) :
    ∃ i, ∃ v ∈ K ℓ.succ i, eval (repl (u ℓ) i v) (P.f i) < eval (u ℓ) (P.f i) := by
  obtain ⟨hfe, -, hne, hU⟩ := hrun.2 ℓ
  obtain ⟨i, hi⟩ := not_ne_improve P (gset_feasible P H hfe.1) hne
  obtain ⟨U, hKU, h1, -⟩ := hU i
  obtain ⟨⟨v, hv⟩, hopt⟩ := h1 hi
  obtain ⟨w, hw, hlt⟩ := hi
  refine ⟨i, v, by rw [hKU]; exact Or.inr hv, ?_⟩
  exact lt_of_le_of_lt ((isMinOn_iff.mp (hopt v hv).2) w hw) hlt

theorem run_inj (hrun : P.IsRun H Θ L K u) {a b : Fin L} (hab : a < b) (heq : u a = u b) :
    False := by
  obtain ⟨i, v, hv, hlt⟩ := run_cut P H Θ hrun a
  have hv' : v ∈ K b.castSucc i :=
    run_mono P H Θ hrun _ _ (Fin.succ_le_castSucc_iff.mpr hab) i hv
  have := ((hrun.2 b).1).2 i v hv'
  rw [← heq] at this
  exact absurd this (not_le.mpr hlt)

theorem run_bound (hrun : P.IsRun H Θ L K u) (hfin : (P.GSet H \ P.NESet).Finite) :
    L ≤ (P.GSet H \ P.NESet).ncard := by
  have hinj : Function.Injective u := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact run_inj P H Θ hrun h hab
    · exact run_inj P H Θ hrun h hab.symm
  have hsub : Set.range u ⊆ P.GSet H \ P.NESet := by
    rintro _ ⟨ℓ, rfl⟩
    exact ⟨((hrun.2 ℓ).1).1, (hrun.2 ℓ).2.2.1⟩
  calc L = (Set.range u).ncard := by rw [Set.ncard_range_of_injective hinj]; simp
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end

/-- One more loop of the algorithm. -/
theorem run_step (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hS : P.Step38Solvable H) {L : ℕ}
    {K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ)} {u : Fin L → Var n → ℝ}
    (hrun : P.IsRun H Θ L K u) {w : Var n → ℝ} (hw : w ∈ P.Feas H (K (Fin.last L)))
    (hwmin : IsMinOn (theta Θ) (P.Feas H (K (Fin.last L))) w) (hwne : ¬ P.IsNE w) :
    ∃ (K'' : Fin (L + 1 + 1) → (i : Fin N) → Set (Fin (n i) → ℝ)) (u'' : Fin (L + 1) → Var n → ℝ),
      P.IsRun H Θ (L + 1) K'' u'' ∧ (∀ t : Fin L, u'' t.castSucc = u t) ∧
      (∀ t : Fin (L + 1), K'' t.castSucc = K t) := by
  classical
  have hwG : w ∈ P.GSet H := hw.1
  let U : (i : Fin N) → Set (Fin (n i) → ℝ) := fun i =>
    if P.CanImprove i w then {Classical.choose (hS w hwG i)} else ∅
  let Knew : (i : Fin N) → Set (Fin (n i) → ℝ) := fun i => K (Fin.last L) i ∪ U i
  refine ⟨Fin.snoc (α := fun _ => (i : Fin N) → Set (Fin (n i) → ℝ)) K Knew,
    Fin.snoc (α := fun _ => Var n → ℝ) u w, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    have : (0 : Fin (L + 1 + 1)) = (0 : Fin (L + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
    exact hrun.1 i
  · intro ℓ
    induction ℓ using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.succ_last, Fin.snoc_castSucc]
      refine ⟨hw, hwmin, hwne, fun i => ⟨U i, rfl, fun hc => ?_, fun hc => ?_⟩⟩
      · simp only [U, if_pos hc]
        refine ⟨Set.singleton_nonempty _, fun v hv => ?_⟩
        rw [Set.mem_singleton_iff] at hv
        rw [hv]; exact Classical.choose_spec (hS w hwG i)
      · simp only [U, if_neg hc]
    | cast ℓ0 =>
      rw [Fin.succ_castSucc]
      simp only [Fin.snoc_castSucc]
      exact hrun.2 ℓ0
  · intro t; exact Fin.snoc_castSucc (α := fun _ => Var n → ℝ) _ _ _
  · intro t; exact Fin.snoc_castSucc (α := fun _ => (i : Fin N) → Set (Fin (n i) → ℝ)) _ _ _

end Sol32Aux

open Sol32Aux in
theorem solution {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1)
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hΘ : Θ.PosDef)
    (hfin : (P.GSet H \ P.NESet).Finite) :
    (∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
        (u : Fin L → Var n → ℝ),
      P.IsRun H Θ L K u → L ≤ (P.GSet H \ P.NESet).ncard) ∧
    (P.Step38Solvable H →
      ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
        (u : Fin L → Var n → ℝ), P.IsRun H Θ L K u →
        ∃ (L' : ℕ) (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
          (u' : Fin L' → Var n → ℝ) (h : L ≤ L'),
          P.RunExtends h K u K' u' ∧ P.IsRun H Θ L' K' u' ∧
            L' ≤ (P.GSet H \ P.NESet).ncard ∧
            P.IsTerminal H Θ (K' (Fin.last L'))) := by
  set B := (P.GSet H \ P.NESet).ncard with hB
  have hbound : ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
      (u : Fin L → Var n → ℝ), P.IsRun H Θ L K u → L ≤ B :=
    fun L K u hrun => run_bound P H Θ hrun hfin
  refine ⟨hbound, fun hS => ?_⟩
  have key : ∀ k : ℕ, ∀ (L : ℕ) (K : Fin (L + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
      (u : Fin L → Var n → ℝ), P.IsRun H Θ L K u → B - L ≤ k →
      ∃ (L' : ℕ) (K' : Fin (L' + 1) → (i : Fin N) → Set (Fin (n i) → ℝ))
        (u' : Fin L' → Var n → ℝ) (h : L ≤ L'),
        P.RunExtends h K u K' u' ∧ P.IsRun H Θ L' K' u' ∧ L' ≤ B ∧
          P.IsTerminal H Θ (K' (Fin.last L')) := by
    intro k
    induction k with
    | zero =>
      intro L K u hrun hk
      refine ⟨L, K, u, le_rfl, ⟨fun t => rfl, fun t => rfl⟩, hrun, hbound L K u hrun, ?_⟩
      by_contra hT
      have hne : (P.Feas H (K (Fin.last L))).Nonempty := by
        by_contra h
        exact hT (Or.inl (Set.not_nonempty_iff_eq_empty.mp h))
      obtain ⟨w, hw, hwmin⟩ := Sol32Fem.feas_min P H _ Θ hΘ hne
      have hwne : ¬ P.IsNE w := fun h => hT (Or.inr ⟨w, hw, hwmin, h⟩)
      obtain ⟨K'', u'', hrun'', -, -⟩ := run_step P H Θ hS hrun hw hwmin hwne
      have := hbound _ _ _ hrun''
      omega
    | succ k ih =>
      intro L K u hrun hk
      by_cases hT : P.IsTerminal H Θ (K (Fin.last L))
      · exact ⟨L, K, u, le_rfl, ⟨fun t => rfl, fun t => rfl⟩, hrun, hbound L K u hrun, hT⟩
      have hne : (P.Feas H (K (Fin.last L))).Nonempty := by
        by_contra h
        exact hT (Or.inl (Set.not_nonempty_iff_eq_empty.mp h))
      obtain ⟨w, hw, hwmin⟩ := Sol32Fem.feas_min P H _ Θ hΘ hne
      have hwne : ¬ P.IsNE w := fun h => hT (Or.inr ⟨w, hw, hwmin, h⟩)
      obtain ⟨K'', u'', hrun'', hu'', hK''⟩ := run_step P H Θ hS hrun hw hwmin hwne
      have hb := hbound _ _ _ hrun''
      obtain ⟨L', K', u', hL, hext, hrun', hL', hT'⟩ := ih (L + 1) K'' u'' hrun'' (by omega)
      refine ⟨L', K', u', by omega, ⟨fun t => ?_, fun t => ?_⟩, hrun', hL', hT'⟩
      · have := hext.1 t.castSucc
        rw [hu''] at this
        exact this
      · have := hext.2 t.castSucc
        rw [hK''] at this
        exact this
  intro L K u hrun
  exact key _ L K u hrun le_rfl
