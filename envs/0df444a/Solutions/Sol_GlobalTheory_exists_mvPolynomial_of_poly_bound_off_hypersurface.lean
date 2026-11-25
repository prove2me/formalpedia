-- Prove2me | solution 1 for GlobalTheory.exists_mvPolynomial_of_poly_bound_off_hypersurface
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:18.821032+00:00
-- url     : https://prove2.me/submissions/dca213ba-2aa7-4790-bcc8-cf86aeb56591

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMvPolynomialOfPolyBoundOffHypersurface
import Theorems.Thm_GlobalTheory_entire_exists_polynomial_of_poly_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PG_eval_lineHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology Asymptotics
namespace GlobalTheory
open Filter Topology Asymptotics in
private theorem norm_cons_le_lemma_4 {d : ℕ} (j : ℂ) (x' : Fin d → ℂ) :
    ‖(Fin.cons j x' : Fin (d + 1) → ℂ)‖ ≤ ‖j‖ + ‖x'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero]; linarith [norm_nonneg x']
  · simp only [Fin.cons_succ]; linarith [norm_le_pi_norm x' i, norm_nonneg j]
open Filter Topology Asymptotics in
private theorem norm_le_of_bound_cons_lemma {d m : ℕ} {C : ℝ} {g : (Fin (d + 1) → ℂ) → ℂ}
    {x : Fin (d + 1) → ℂ} (j : ℂ) (x' : Fin d → ℂ) (hx : x = Fin.cons j x')
    (h : ‖g x‖ ≤ C * (1 + ‖x‖) ^ m) :
    ‖g x‖ ≤ |C| * (1 + ‖j‖) ^ m * (1 + ‖x'‖) ^ m := by
  have h1 : 1 + ‖x‖ ≤ (1 + ‖j‖) * (1 + ‖x'‖) := by
    have := norm_cons_le_lemma_4 j x'
    rw [← hx] at this
    nlinarith [norm_nonneg j, norm_nonneg x']
  calc ‖g x‖ ≤ C * (1 + ‖x‖) ^ m := h
    _ ≤ |C| * (1 + ‖x‖) ^ m := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + ‖j‖) * (1 + ‖x'‖)) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 m) (abs_nonneg C)
    _ = |C| * (1 + ‖j‖) ^ m * (1 + ‖x'‖) ^ m := by rw [mul_pow, mul_assoc]
open Filter Topology Asymptotics in
private theorem polynomial_of_bound_off_roots_lemma_2 {m : ℕ} {K : ℝ} :
    ∀ (n : ℕ) (r : Polynomial ℂ) (g : ℂ → ℂ), r.natDegree = n → r ≠ 0 →
      DifferentiableOn ℂ g {s | r.eval s ≠ 0} →
      (∀ s, r.eval s ≠ 0 → ‖g s‖ ≤ K * (1 + ‖s‖) ^ m) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ s, r.eval s ≠ 0 → g s = p.eval s := by
  intro n
  induction n with
  | zero =>
    intro r g hn hr hg hb
    have hc : ∀ s, r.eval s ≠ 0 := by
      intro s h0
      apply hr
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.eval_C] at h0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn, h0, map_zero]
    have hU : {s | r.eval s ≠ 0} = Set.univ := Set.eq_univ_of_forall hc
    rw [hU] at hg
    obtain ⟨p, hp, hgp⟩ :=
      _root_.GlobalTheory.entire_exists_polynomial_of_poly_bound (differentiableOn_univ.mp hg) (C := K) (m := m)
        (fun z => hb z (hc z))
    exact ⟨p, hp, fun s _ => hgp s⟩
  | succ n ih =>
    intro r g hn hr hg hb
    obtain ⟨c, hc⟩ := Complex.exists_root (f := r) (by
      rw [Polynomial.degree_eq_natDegree hr, hn]; exact_mod_cast Nat.succ_pos n)
    set r' := r /ₘ (Polynomial.X - Polynomial.C c) with hr'def
    have hfac : (Polynomial.X - Polynomial.C c) * r' = r :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hc
    have hr'0 : r' ≠ 0 := by
      rintro h; apply hr; rw [← hfac, h, mul_zero]
    have hdeg : r'.natDegree = n := by
      have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero c) hr'0
      rw [hfac, hn, Polynomial.natDegree_X_sub_C] at this
      omega
    have heval : ∀ z, r.eval z = (z - c) * r'.eval z := by
      intro z; rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
    have hopen : IsOpen {z : ℂ | r'.eval z ≠ 0} :=
      isOpen_ne_fun (Polynomial.continuous r') continuous_const
    have hopenr : IsOpen {z : ℂ | r.eval z ≠ 0} :=
      isOpen_ne_fun (Polynomial.continuous r) continuous_const
    set g' := Function.update g c (limUnder (𝓝[≠] c) g) with hg'def
    have hoff : ∀ z, z ≠ c → g' z = g z := fun z hz => Function.update_of_ne hz _ _
    have key : r'.eval c ≠ 0 → DifferentiableAt ℂ g' c ∧ ‖g' c‖ ≤ K * (1 + ‖c‖) ^ m := by
      intro hc'
      set S := {z : ℂ | r'.eval z ≠ 0} ∩ Metric.ball c 1 with hSdef
      have hSn : S ∈ 𝓝 c :=
        (hopen.inter Metric.isOpen_ball).mem_nhds ⟨hc', Metric.mem_ball_self one_pos⟩
      have hS : DifferentiableOn ℂ g (S \ {c}) := by
        refine hg.mono ?_
        rintro z ⟨⟨hz1, -⟩, hz2⟩
        show r.eval z ≠ 0
        rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz2) hz1
      have hbdd : BddAbove (norm ∘ g '' (S \ {c})) := by
        refine ⟨|K| * (2 + ‖c‖) ^ m, ?_⟩
        rintro _ ⟨z, ⟨⟨hz1, hz3⟩, hz2⟩, rfl⟩
        have hrz : r.eval z ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz2) hz1
        have hzc : ‖z - c‖ < 1 := mem_ball_iff_norm.mp hz3
        have hzn : ‖z‖ ≤ 1 + ‖c‖ := by
          have := norm_sub_norm_le z c; linarith
        calc ‖g z‖ ≤ K * (1 + ‖z‖) ^ m := hb z hrz
          _ ≤ |K| * (1 + ‖z‖) ^ m := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
          _ ≤ |K| * (2 + ‖c‖) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) m)
              (abs_nonneg K)
      have hU := Complex.differentiableOn_update_limUnder_of_bddAbove hSn hS hbdd
      have hd : DifferentiableAt ℂ g' c := (hU c (mem_of_mem_nhds hSn)).differentiableAt hSn
      refine ⟨hd, ?_⟩
      have hcont : ContinuousAt (fun z => ‖g' z‖ - K * (1 + ‖z‖) ^ m) c :=
        hd.continuousAt.norm.sub (by fun_prop)
      have hev : ∀ᶠ z in 𝓝[≠] c, ‖g' z‖ - K * (1 + ‖z‖) ^ m ≤ 0 := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hSn] with z hzc hzS
        have hz : z ≠ c := hzc
        have hrz : r.eval z ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hz) hzS.1
        rw [hoff z hz]
        linarith [hb z hrz]
      have := le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
      linarith
    have hdiff : DifferentiableOn ℂ g' {s | r'.eval s ≠ 0} := by
      intro s hs
      by_cases hsc : s = c
      · subst hsc
        exact (key hs).1.differentiableWithinAt
      · have hrs : r.eval s ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hsc) hs
        have hgs : DifferentiableAt ℂ g s := (hg s hrs).differentiableAt (hopenr.mem_nhds hrs)
        have heq : g =ᶠ[𝓝 s] g' :=
          Filter.eventuallyEq_of_mem (isOpen_ne.mem_nhds hsc) (fun z hz => (hoff z hz).symm)
        exact (hgs.congr_of_eventuallyEq heq.symm).differentiableWithinAt
    have hbound : ∀ s, r'.eval s ≠ 0 → ‖g' s‖ ≤ K * (1 + ‖s‖) ^ m := by
      intro s hs
      by_cases hsc : s = c
      · subst hsc; exact (key hs).2
      · have hrs : r.eval s ≠ 0 := by
          rw [heval]; exact mul_ne_zero (sub_ne_zero.mpr hsc) hs
        rw [hoff s hsc]; exact hb s hrs
    obtain ⟨p, hp, hgp⟩ := ih r' g' hdeg hr'0 hdiff hbound
    refine ⟨p, hp, fun s hs => ?_⟩
    have hsc : s ≠ c := by
      rintro rfl; apply hs; rw [heval, sub_self, zero_mul]
    have hs' : r'.eval s ≠ 0 := by
      intro h0; apply hs; rw [heval, h0, mul_zero]
    rw [← hoff s hsc]; exact hgp s hs'
open Filter Topology Asymptotics in
private theorem polynomial_eventually_ne_zero_lemma_3 {ρ : Polynomial ℂ} (hρ : ρ ≠ 0) (a : ℂ) :
    ∀ᶠ t in 𝓝[≠] a, ρ.eval t ≠ 0 := by
  have hU : IsOpen ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl
  have ha : a ∈ ((↑(ρ.roots.toFinset.erase a) : Set ℂ)ᶜ) := by simp
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds ha)] with t ht htU h0
  apply htU
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Polynomial.mem_roots hρ, Polynomial.IsRoot.def, h0, Set.mem_singleton_iff, true_and]
  exact ht
end GlobalTheory
end

set_option autoImplicit false
open Filter Topology Asymptotics
open GlobalTheory
open Filter Topology Asymptotics
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 →
        f x = MvPolynomial.eval x p := by
  intro d
  induction d with
  | zero =>
    intro m q f C _ _ _
    refine ⟨MvPolynomial.C (f 0), fun x _ => ?_⟩
    rw [MvPolynomial.eval_C, Subsingleton.elim x 0]
  | succ d ih =>
    intro m q f C hq hf hb
    set Q := MvPolynomial.finSuccEquiv ℂ d q with hQ
    have hQ0 : Q ≠ 0 := by
      rw [hQ]; exact (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).mpr hq
    set qs : ℂ → MvPolynomial (Fin d) ℂ := fun j => Polynomial.eval (MvPolynomial.C j) Q
      with hqsdef
    have hqs : ∀ j x', MvPolynomial.eval x' (qs j) = MvPolynomial.eval (Fin.cons j x') q := by
      intro j x'
      rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map, hqsdef,
        ← Polynomial.eval₂_hom, MvPolynomial.eval_C]
    have hopen : IsOpen {x : Fin (d + 1) → ℂ | MvPolynomial.eval x q ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const
    set B := {j : ℂ | qs j = 0} with hBdef
    have hB : B.Finite := by
      refine ((Q.roots.toFinset.finite_toSet).preimage
        (MvPolynomial.C_injective (Fin d) ℂ).injOn).subset ?_
      intro j hj
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
        Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]
      exact hj
    set emb := hB.infinite_compl.natEmbedding
    set v : ℕ → ℂ := fun k => (emb k : ℂ) with hvdef
    have hvinj : Function.Injective v := Subtype.val_injective.comp emb.injective
    have hvB : ∀ k, qs (v k) ≠ 0 := fun k => (emb k).2
    have hnode : ∀ k, ∃ P : MvPolynomial (Fin d) ℂ, ∀ x' : Fin d → ℂ,
        MvPolynomial.eval x' (qs (v k)) ≠ 0 → f (Fin.cons (v k) x') = MvPolynomial.eval x' P := by
      intro k
      refine ih m (qs (v k)) (fun x' => f (Fin.cons (v k) x')) (|C| * (1 + ‖v k‖) ^ m) (hvB k)
        ?_ ?_
      · have hc : Differentiable ℂ (fun x' : Fin d → ℂ => (Fin.cons (v k) x' : Fin (d + 1) → ℂ)) :=
          differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_const (v k))
            (fun i => by simpa using differentiable_apply i) i
        refine hf.comp hc.differentiableOn ?_
        intro x' hx'
        show MvPolynomial.eval (Fin.cons (v k) x') q ≠ 0
        rw [← hqs]; exact hx'
      · intro x' hx'
        rw [hqs] at hx'
        have := norm_le_of_bound_cons_lemma (v k) x' rfl (hb _ hx')
        simpa using this
    choose P hP using hnode
    set s := Finset.range (m + 1) with hsdef
    set Pm : MvPolynomial (Fin (d + 1)) ℂ := ∑ k ∈ s,
      Polynomial.aeval (MvPolynomial.X 0) (Lagrange.basis s v k) *
        MvPolynomial.rename Fin.succ (P k) with hPmdef
    have hPm : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x Pm =
        ∑ k ∈ s, (Lagrange.basis s v k).eval (x 0) * MvPolynomial.eval (Fin.tail x) (P k) := by
      intro x
      have hA : ∀ φ : Polynomial ℂ,
          MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0) φ) = φ.eval (x 0) := by
        intro φ
        induction φ using Polynomial.induction_on' with
        | add p₁ p₂ h₁ h₂ => simp only [map_add, Polynomial.eval_add, h₁, h₂]
        | monomial n a => simp [Polynomial.aeval_monomial, Polynomial.eval_monomial]
      rw [hPmdef, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_rename, hA]
      rfl
    have hgen : ∀ x : Fin (d + 1) → ℂ, MvPolynomial.eval x q ≠ 0 →
        (∀ k ∈ s, MvPolynomial.eval (Fin.tail x) (qs (v k)) ≠ 0) →
        f x = MvPolynomial.eval x Pm := by
      intro x hx hxs
      set x' := Fin.tail x
      have hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x := Fin.cons_self_tail x
      set r := Polynomial.map (MvPolynomial.eval x') Q with hrdef
      have hr : ∀ t, r.eval t = MvPolynomial.eval (Fin.cons t x') q := by
        intro t; rw [MvPolynomial.eval_eq_eval_mv_eval']
      have hr0 : r ≠ 0 := by
        intro h0; apply hx; rw [← hxc, ← hr, h0, Polynomial.eval_zero]
      have hc : Differentiable ℂ (fun t : ℂ => (Fin.cons t x' : Fin (d + 1) → ℂ)) :=
        differentiable_pi.2 fun i => Fin.cases (by simpa using differentiable_id)
          (fun i => by simpa using differentiable_const (x' i)) i
      obtain ⟨φ, hφdeg, hφ⟩ := polynomial_of_bound_off_roots_lemma_2 (m := m) (K := |C| * (1 + ‖x'‖) ^ m)
        r.natDegree r (fun t => f (Fin.cons t x')) rfl hr0
        (hf.comp hc.differentiableOn (fun t ht => by
          show MvPolynomial.eval (Fin.cons t x') q ≠ 0
          rw [← hr]; exact ht))
        (fun t ht => by
          rw [hr] at ht
          have := norm_le_of_bound_cons_lemma t x' rfl (hb _ ht)
          calc _ ≤ _ := this
            _ = _ := by ring)
      have hinterp := Lagrange.eq_interpolate (s := s) (v := v) (f := φ) hvinj.injOn
        (by
          rw [hsdef, Finset.card_range]
          exact (Polynomial.degree_le_of_natDegree_le hφdeg).trans_lt
            (by exact_mod_cast Nat.lt_succ_self m))
      have hx0 : f x = φ.eval (x 0) := by
        have := hφ (x 0) (by rw [hr, hxc]; exact hx)
        rw [← this, hxc]
      rw [hx0, hinterp, Lagrange.interpolate_apply, Polynomial.eval_finset_sum, hPm]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
      congr 1
      have hk' : r.eval (v k) ≠ 0 := by rw [hr, ← hqs]; exact hxs k hk
      rw [← hφ (v k) hk']
      exact hP k x' (hxs k hk)
    refine ⟨Pm, fun x hx => ?_⟩
    set x' := Fin.tail x
    have hxc : (Fin.cons (x 0) x' : Fin (d + 1) → ℂ) = x := Fin.cons_self_tail x
    set R := ∏ k ∈ s, qs (v k) with hRdef
    have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hvB k
    obtain ⟨y, hy⟩ : ∃ y, MvPolynomial.eval y R ≠ 0 := by
      by_contra h
      push_neg at h
      exact hR0 (MvPolynomial.funext fun y => by rw [h y, map_zero])
    set w : Fin d → ℂ := y - x'
    set ρ := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.lineHom x' w R
    have hρ : ∀ t, ρ.eval t = MvPolynomial.eval (fun i => x' i + w i * t) R :=
      fun t => _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom x' w R t
    have hρ0 : ρ ≠ 0 := by
      intro h0
      apply hy
      have := hρ 1
      rw [h0, Polynomial.eval_zero] at this
      have hy' : (fun i => x' i + w i * 1) = y := by
        funext i; simp [w]
      rw [hy'] at this
      exact this.symm
    set γ : ℂ → Fin (d + 1) → ℂ := fun t => Fin.cons (x 0) (fun i => x' i + w i * t)
    have hγ : Continuous γ := by
      refine continuous_pi fun i => Fin.cases ?_ (fun i => ?_) i
      · simpa [γ] using continuous_const
      · simp only [γ, Fin.cons_succ]; fun_prop
    have hγ0 : γ 0 = x := by
      simp only [γ, mul_zero, add_zero]; exact hxc
    have hfx : ContinuousAt f x :=
      (hf x hx).continuousWithinAt.continuousAt (hopen.mem_nhds hx)
    have hγc : Tendsto γ (𝓝 0) (𝓝 x) := by
      have := hγ.tendsto 0
      rwa [hγ0] at this
    have h1 : Tendsto (fun t => f (γ t)) (𝓝[≠] 0) (𝓝 (f x)) :=
      (hfx.tendsto.comp hγc).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t => MvPolynomial.eval (γ t) Pm) (𝓝[≠] 0)
        (𝓝 (MvPolynomial.eval x Pm)) :=
      ((MvPolynomial.continuous_eval Pm).continuousAt.tendsto.comp hγc).mono_left
        nhdsWithin_le_nhds
    have hq : ∀ᶠ t in 𝓝[≠] (0 : ℂ), MvPolynomial.eval (γ t) q ≠ 0 := by
      have hcq : ContinuousAt (fun t => MvPolynomial.eval (γ t) q) 0 :=
        ((MvPolynomial.continuous_eval q).comp hγ).continuousAt
      have := hcq.eventually_ne (by simpa [hγ0] using hx)
      exact this.filter_mono nhdsWithin_le_nhds
    have heq : (fun t => f (γ t)) =ᶠ[𝓝[≠] 0] (fun t => MvPolynomial.eval (γ t) Pm) := by
      filter_upwards [hq, polynomial_eventually_ne_zero_lemma_3 hρ0 0] with t ht hρt
      refine hgen (γ t) ht fun k hk => ?_
      rw [hρ, hRdef, map_prod] at hρt
      have := Finset.prod_ne_zero_iff.mp hρt k hk
      simpa [γ, Fin.tail_cons] using this
    exact tendsto_nhds_unique_of_eventuallyEq h1 h2 heq
end _root_.GlobalTheory
end GlobalTheory
