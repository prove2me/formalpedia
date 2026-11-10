-- Prove2me | solution 1 for IntLInfty.Kan.crForms_eq_jet_image
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:57:13.964782+00:00
-- url     : https://prove2.me/submissions/45ef357d-0128-4548-b2cc-f6f59319e552

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

set_option autoImplicit false
set_option maxHeartbeats 400000


namespace IntLInfty.Kan.A83D2

open MeasureTheory Filter Topology
open scoped ContDiff

variable {m : ℕ}

end IntLInfty.Kan.A83D2

namespace IntLInfty.Kan.A83

open IntLInfty.Kan

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

section FormsLin

theorem convex_simplex (m : ℕ) : Convex ℝ (simplex m) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx.2, hy.2]

theorem interior_simplex_nonempty (m : ℕ) : (interior (simplex m)).Nonempty := by
  let U : Set (Fin m → ℝ) := {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1}
  have hU : IsOpen U := by
    have h1 : IsOpen {t : Fin m → ℝ | ∀ i, 0 < t i} := by
      simpa only [Set.ofPred_forall] using
        isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have h2 : IsOpen {t : Fin m → ℝ | ∑ i, t i < 1} :=
      isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  have hsub : U ⊆ simplex m := fun t ht => ⟨fun i => (ht.1 i).le, ht.2.le⟩
  refine ⟨fun _ => 1 / ((m : ℝ) + 1), interior_mono hsub (hU.interior_eq.symm ▸ ?_)⟩
  refine ⟨fun i => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

theorem uniqueDiffOn_simplex (m : ℕ) : UniqueDiffOn ℝ (simplex m) :=
  uniqueDiffOn_convex (convex_simplex m) (interior_simplex_nonempty m)

theorem coeff_add {m : ℕ} (ω ω' : Ω m) (I : Finset (Fin m)) :
    coeff (ω + ω') I = coeff ω I + coeff ω' I := by
  funext x; simp [coeff]

theorem coeff_smul {m : ℕ} (c : ℝ) (ω : Ω m) (I : Finset (Fin m)) :
    coeff (c • ω) I = c • coeff ω I := by
  funext x; simp [coeff]

theorem jetComp_congr {m k : ℕ} {f g : (Fin m → ℝ) → ℝ} (h : Set.EqOn f g (simplex m))
    (β : Fin k → Fin m) : jetComp f k β = jetComp g k β := by
  have he : Set.EqOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (fun x => iteratedFDerivWithin ℝ k g (simplex m) x fun l => Pi.single (β l) 1) (simplex m) :=
    fun x hx => by simp only [iteratedFDerivWithin_congr h hx]
  unfold jetComp
  split_ifs with h1 h2 h2
  · ext x; simp [BoundedContinuousFunction.mkOfCompact_apply, he x.2]
  · exact absurd (h1.congr he.symm) h2
  · exact absurd (h2.congr he) h1
  · rfl

theorem contOn_iter {m k r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r)
    (β : Fin k → Fin m) :
    ContinuousOn (fun x => iteratedFDerivWithin ℝ k f (simplex m) x fun l => Pi.single (β l) 1)
      (simplex m) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin m → ℝ) ℝ
      (fun l => Pi.single (β l) 1)).continuous.comp_continuousOn
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) (uniqueDiffOn_simplex m))

theorem jetComp_add {m k r : ℕ} {f g : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hg : ContDiffOn ℝ r g (simplex m)) (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (f + g) k β = jetComp f k β + jetComp g k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  have hgk : ContDiffOn ℝ k g (simplex m) := hg.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := f + g) (hf.add hg) hk β), dif_pos (contOn_iter hf hk β),
    dif_pos (contOn_iter hg hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_add,
    Pi.add_apply, ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (f + g) (simplex m) x.1) _ =
    (iteratedFDerivWithin ℝ k f (simplex m) x.1) _ + (iteratedFDerivWithin ℝ k g (simplex m) x.1) _
  rw [iteratedFDerivWithin_add_apply (hfk x.1 x.2) (hgk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

theorem jetComp_smul {m k r : ℕ} (c : ℝ) {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m))
    (hk : k ≤ r) (β : Fin k → Fin m) :
    jetComp (c • f) k β = c • jetComp f k β := by
  have hfk : ContDiffOn ℝ k f (simplex m) := hf.of_le (by exact_mod_cast hk)
  unfold jetComp
  rw [dif_pos (contOn_iter (f := c • f) (hf.const_smul c) hk β), dif_pos (contOn_iter hf hk β)]
  ext x
  simp only [BoundedContinuousFunction.mkOfCompact_apply, BoundedContinuousFunction.coe_smul,
    ContinuousMap.coe_mk]
  change (iteratedFDerivWithin ℝ k (c • f) (simplex m) x.1) _ =
    c • (iteratedFDerivWithin ℝ k f (simplex m) x.1) _
  rw [iteratedFDerivWithin_const_smul_apply (hfk x.1 x.2) (uniqueDiffOn_simplex m) x.2]
  rfl

end FormsLin

section FormsLin2

variable {m r : ℕ}

theorem extD_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (ω + ω') x = extD ω x + extD ω' x := by
  have hd : ∀ η : Ω m, IsCr r η → ∀ I, DifferentiableWithinAt ℝ (coeff η I) (simplex m) x :=
    fun η h I => ((h I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  simp only [extD, coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_add (uniqueDiffOn_simplex m x hx) (hd ω hω I) (hd ω' hω' I)]
  simp [add_smul]

theorem extD_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (c • ω) x = c • extD ω x := by
  have hd : ∀ I, DifferentiableWithinAt ℝ (coeff ω I) (simplex m) x :=
    fun I => ((hω I).1.differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) x hx
  have e : ∀ I, fderivWithin ℝ (c • coeff ω I) (simplex m) x =
      c • fderivWithin ℝ (coeff ω I) (simplex m) x :=
    fun I => fderivWithin_const_smul (uniqueDiffOn_simplex m x hx) (hd I) c
  simp only [extD, coeff_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_smul_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e I, ContinuousLinearMap.smul_apply, smul_assoc]

theorem isDeg_add {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω') : IsDeg n (ω + ω') :=
  fun x hx => Submodule.add_mem _ (h x hx) (h' x hx)

theorem isDeg_smul {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω) : IsDeg n (c • ω) :=
  fun x hx => Submodule.smul_mem _ c (h x hx)

theorem isCr_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') : IsCr r (ω + ω') := by
  intro I
  refine ⟨by rw [coeff_add]; exact (hω I).1.add (hω' I).1, ((hω I).2.add (hω' I).2).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
  rw [extD_add hr hω hω' hx, map_add]; rfl

theorem isCr_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) : IsCr r (c • ω) := by
  intro I
  refine ⟨by rw [coeff_smul]; exact (hω I).1.const_smul c, ((hω I).2.const_smul c).congr ?_⟩
  intro x hx
  show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
  rw [extD_smul hr c hω hx, map_smul]; rfl

theorem jet_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') :
    jet r (ω + ω') = jet r ω + jet r ω' := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (ω + ω') I) k β = jetComp (coeff ω I) k β + jetComp (coeff ω' I) k β
    rw [coeff_add, jetComp_add (hω I).1 (hω' I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (ω + ω')) I) k β =
      jetComp (coeff (extD ω) I) k β + jetComp (coeff (extD ω') I) k β
    rw [jetComp_congr (g := coeff (extD ω) I + coeff (extD ω') I) (fun x hx => by
        show (formBasis m).repr (extD (ω + ω') x) I = coeff (extD ω) I x + coeff (extD ω') I x
        rw [extD_add hr hω hω' hx, map_add]; rfl),
      jetComp_add (hω I).2 (hω' I).2 (Nat.lt_succ_iff.mp k.2)]

theorem jet_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) :
    jet r (c • ω) = c • jet r ω := by
  refine Prod.ext (funext fun I => funext fun k => funext fun β => ?_)
    (funext fun I => funext fun k => funext fun β => ?_)
  · show jetComp (coeff (c • ω) I) k β = c • jetComp (coeff ω I) k β
    rw [coeff_smul, jetComp_smul c (hω I).1 (Nat.lt_succ_iff.mp k.2)]
  · show jetComp (coeff (extD (c • ω)) I) k β = c • jetComp (coeff (extD ω) I) k β
    rw [jetComp_congr (g := c • coeff (extD ω) I) (fun x hx => by
        show (formBasis m).repr (extD (c • ω) x) I = c • coeff (extD ω) I x
        rw [extD_smul hr c hω hx, map_smul]; rfl),
      jetComp_smul c (hω I).2 (Nat.lt_succ_iff.mp k.2)]

theorem isCr_zero : IsCr r (0 : Ω m) := by
  intro I
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  have h1 : extD (0 : Ω m) = 0 := by funext x; simp [extD, h0]
  refine ⟨by rw [h0]; exact contDiffOn_const, by rw [h1, h0]; exact contDiffOn_const⟩

theorem isDeg_zero {n : ℕ} : IsDeg n (0 : Ω m) := fun _ _ => Submodule.zero_mem _

/-- The span in the definition of `CrForms` adds nothing: it is already the image of the jet map. -/
theorem span_jet_eq (hr : 1 ≤ r) (n : ℕ) :
    ((Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) : Submodule ℝ _) :
      Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  refine le_antisymm (fun w hw => ?_) Submodule.subset_span
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, ⟨isDeg_zero, isCr_zero⟩, ?_⟩
    have := jet_smul (m := m) hr 0 (isCr_zero (m := m) (r := r))
    simpa using this
  | add a b _ _ ha hb =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ω', ⟨h1', h2'⟩, rfl⟩ := hb
    exact ⟨ω + ω', ⟨isDeg_add h1 h1', isCr_add hr h2 h2'⟩, jet_add hr h2 h2'⟩
  | smul c a _ ha =>
    obtain ⟨ω, ⟨h1, h2⟩, rfl⟩ := ha
    exact ⟨c • ω, ⟨isDeg_smul c h1, isCr_smul hr c h2⟩, jet_smul hr c h2⟩

theorem crForms_coe (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = closure (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  rw [CrForms, Submodule.topologicalClosure_coe, span_jet_eq hr n]

end FormsLin2

open Filter Topology

section TaylorLimit

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem tendstoUniformlyOn_curryLeft {S : Set E} {j : ℕ}
    {q : ℕ → E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    {Q : E → ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F}
    (h : TendstoUniformlyOn q Q atTop S) :
    TendstoUniformlyOn (fun k x => (q k x).curryLeft) (fun x => (Q x).curryLeft) atTop S := by
  have hu : UniformContinuous
      (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin (j + 1) => E) F => A.curryLeft) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).isometry.uniformContinuous
  exact hu.comp_tendstoUniformlyOn h

theorem taylor_limit {S : Set E} (hconv : Convex ℝ S) (hcl : closure (interior S) = S) {r : ℕ}
    {f : ℕ → E → F} {p : ℕ → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k, HasFTaylorSeriesUpToOn r (f k) (p k) S)
    {P : E → FormalMultilinearSeries ℝ E F}
    (hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => p k x j) (fun x => P x j) atTop S) :
    HasFTaylorSeriesUpToOn r (fun x => (P x 0).curry0) P S := by
  have hcont : ∀ j ≤ r, ContinuousOn (fun x => P x j) S := fun j hj =>
    (hP j hj).continuousOn (Eventually.frequently (Eventually.of_forall fun k =>
      (hp k).cont j (by exact_mod_cast hj)))
  refine ⟨fun x _ => rfl, ?_, fun j hj => hcont j (by exact_mod_cast hj)⟩
  intro j hj x hx
  have hj' : j + 1 ≤ r := by exact_mod_cast hj
  set s := interior S with hs_def
  have hso : IsOpen s := isOpen_interior
  have hsc : Convex ℝ s := hconv.interior
  have hsS : s ⊆ S := interior_subset
  have hder : ∀ y ∈ s, HasFDerivAt (fun x => P x j) (P y (j + 1)).curryLeft y := by
    intro y hy
    refine hasFDerivAt_of_tendstoUniformlyOn (l := atTop) hso
      (f := fun k x => p k x j) (f' := fun k x => (p k x (j + 1)).curryLeft)
      ((tendstoUniformlyOn_curryLeft ((hP (j + 1) hj').mono hsS))) ?_ ?_ hy
    · intro k z hz
      exact ((hp k).fderivWithin j (by exact_mod_cast hj) z (hsS hz)).hasFDerivAt
        (mem_interior_iff_mem_nhds.mp hz)
    · intro z hz
      exact (hP j (by omega)).tendsto_at (hsS hz)
  have hG'cont : ContinuousOn (fun x => (P x (j + 1)).curryLeft) S := by
    have := hcont (j + 1) hj'
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).continuous.comp_continuousOn
      this
  have key := hasFDerivWithinAt_closure_of_tendsto_fderiv (f := fun x => P x j)
    (f' := (P x (j + 1)).curryLeft) (x := x)
    (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt) hsc hso
    (fun y hy => by
      rw [hcl] at hy
      exact ((hcont j (by omega)) y hy).mono hsS)
    (by
      have h1 : Tendsto (fun y => (P y (j + 1)).curryLeft) (𝓝[s] x) (𝓝 (P x (j + 1)).curryLeft) :=
        ((hG'cont x hx).mono hsS).tendsto
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder y hy).fderiv.symm)
  rwa [hcl] at key

end TaylorLimit

section JetLimit

open IntLInfty.Kan BoundedContinuousFunction

theorem isClosed_simplex (m : ℕ) : IsClosed (simplex m) := by
  have h1 : IsClosed {t : Fin m → ℝ | ∀ i, 0 ≤ t i} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {t : Fin m → ℝ | ∑ i, t i ≤ 1} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem closure_interior_simplex (m : ℕ) : closure (interior (simplex m)) = simplex m := by
  rw [(convex_simplex m).closure_interior_eq_closure_of_nonempty_interior
    (interior_simplex_nonempty m)]
  exact (isClosed_simplex m).closure_eq

theorem jetComp_apply {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1) := by
  unfold jetComp
  rw [dif_pos (contOn_iter hf hk β)]
  rfl

theorem norm_cmm_le_sum {m j : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin m → ℝ) ℝ) :
    ‖M‖ ≤ ∑ β : Fin j → Fin m, |M (fun l => Pi.single (β l) 1)| := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun v => ?_
  have hv : v = fun l => ∑ i : Fin m, v l i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    funext l; ext t; simp [Finset.sum_apply, Pi.single_apply]
  have hexp : M v = ∑ β : Fin j → Fin m, (∏ l, v l (β l)) • M (fun l => Pi.single (β l) 1) := by
    conv_lhs => rw [hv]
    rw [M.map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact M.map_smul_univ _ _
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [norm_smul, norm_prod, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun l _ => norm_le_pi_norm (v l) (β l)) (abs_nonneg _)

/-- Sub-lemma A: a limit (in the jet norm) of jets of `Cʳ` functions on the simplex is the jet of a
`Cʳ` function. -/
theorem jet_limit {m r : ℕ} {f : ℕ → (Fin m → ℝ) → ℝ} (hf : ∀ k, ContDiffOn ℝ r (f k) (simplex m))
    {g : (j : Fin (r + 1)) → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ)}
    (hg : ∀ (j : Fin (r + 1)) β, Tendsto (fun k => jetComp (f k) j β) atTop (𝓝 (g j β))) :
    ∃ F : (Fin m → ℝ) → ℝ, ContDiffOn ℝ r F (simplex m) ∧
      ∀ (j : Fin (r + 1)) β, jetComp F j β = g j β := by
  have hU : UniqueDiffOn ℝ (simplex m) := uniqueDiffOn_simplex m
  have hCau : ∀ j : Fin (r + 1),
      UniformCauchySeqOn (fun k x => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (simplex m) := by
    intro j
    let J : ℕ → (Fin (j : ℕ) → Fin m) → (simplex m →ᵇ ℝ) := fun k β => jetComp (f k) j β
    have hJ : Tendsto J atTop (𝓝 fun β => g j β) := tendsto_pi_nhds.mpr fun β => hg j β
    have hJc := hJ.cauchySeq
    rw [Metric.cauchySeq_iff] at hJc
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set c : ℝ := (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) + 1 with hc_def
    have hc : 0 < c := by positivity
    obtain ⟨N, hN⟩ := hJc (ε / c) (div_pos hε hc)
    refine ⟨N, fun a ha b hb x hx => ?_⟩
    have hab := hN a ha b hb
    rw [dist_eq_norm] at hab ⊢
    refine lt_of_le_of_lt (norm_cmm_le_sum _) ?_
    have hterm : ∀ β : Fin (j : ℕ) → Fin m,
        |(iteratedFDerivWithin ℝ j (f a) (simplex m) x - iteratedFDerivWithin ℝ j (f b) (simplex m) x)
          (fun l => Pi.single (β l) 1)| ≤ ε / c := by
      intro β
      rw [_root_.sub_apply, ← jetComp_apply (hf a) (Fin.is_le j) β hx,
        ← jetComp_apply (hf b) (Fin.is_le j) β hx]
      calc |jetComp (f a) j β ⟨x, hx⟩ - jetComp (f b) j β ⟨x, hx⟩|
          = ‖(J a β - J b β) ⟨x, hx⟩‖ := by rw [Real.norm_eq_abs]; rfl
        _ ≤ ‖J a β - J b β‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ ‖J a - J b‖ := norm_le_pi_norm (J a - J b) β
        _ ≤ ε / c := hab.le
    calc ∑ β : Fin (j : ℕ) → Fin m, |(iteratedFDerivWithin ℝ j (f a) (simplex m) x -
          iteratedFDerivWithin ℝ j (f b) (simplex m) x) (fun l => Pi.single (β l) 1)|
        ≤ ∑ _β : Fin (j : ℕ) → Fin m, ε / c := Finset.sum_le_sum fun β _ => hterm β
      _ = (Fintype.card (Fin (j : ℕ) → Fin m) : ℝ) * (ε / c) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < c * (ε / c) := by
          apply mul_lt_mul_of_pos_right _ (div_pos hε hc)
          rw [hc_def]; linarith
      _ = ε := by field_simp
  let P : (Fin m → ℝ) → FormalMultilinearSeries ℝ (Fin m → ℝ) ℝ := fun x j =>
    limUnder atTop (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x)
  have hPt : ∀ j : Fin (r + 1), ∀ x ∈ (simplex m),
      Tendsto (fun k => iteratedFDerivWithin ℝ j (f k) (simplex m) x) atTop (𝓝 (P x j)) :=
    fun j x hx => ((hCau j).cauchySeq hx).tendsto_limUnder
  have hP : ∀ j ≤ r, TendstoUniformlyOn (fun k x => ftaylorSeriesWithin ℝ (f k) (simplex m) x j)
      (fun x => P x j) atTop (simplex m) := by
    intro j hj
    exact (hCau ⟨j, Nat.lt_succ_of_le hj⟩).tendstoUniformlyOn_of_tendsto
      (hPt ⟨j, Nat.lt_succ_of_le hj⟩)
  have H := taylor_limit (convex_simplex m) (closure_interior_simplex m)
    (fun k => (hf k).ftaylorSeriesWithin hU) hP
  have hFc : ContDiffOn ℝ r (fun x => (P x 0).curry0) (simplex m) := H.contDiffOn
  refine ⟨fun x => (P x 0).curry0, hFc, fun j β => ?_⟩
  ext ⟨x, hx⟩
  rw [jetComp_apply hFc (Fin.is_le j) β hx,
    ← H.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast Fin.is_le j) hU hx]
  have h1 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop (𝓝 (g j β ⟨x, hx⟩)) :=
    ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (hg j β)
  have h2 : Tendsto (fun k => jetComp (f k) j β ⟨x, hx⟩) atTop
      (𝓝 (P x j (fun l => Pi.single (β l) 1))) := by
    have := ((continuous_eval_const (fun l => Pi.single (β l) (1 : ℝ))).tendsto
      _).comp (hPt j x hx)
    refine this.congr fun k => ?_
    exact (jetComp_apply (hf k) (Fin.is_le j) β hx).symm
  exact tendsto_nhds_unique h2 h1

end JetLimit

section JetClosed

open IntLInfty.Kan BoundedContinuousFunction

theorem jetComp_zero {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
    (hk : k = 0) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f k β ⟨x, hx⟩ = f x := by
  subst hk
  rw [jetComp_apply hf (Nat.zero_le _) β hx]
  rfl

theorem jetComp_one {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) (hr : 1 ≤ r)
    (β : Fin 1 → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    jetComp f 1 β ⟨x, hx⟩ = fderivWithin ℝ f (simplex m) x (Pi.single (β 0) 1) := by
  rw [jetComp_apply hf hr β hx, iteratedFDerivWithin_one_apply (uniqueDiffOn_simplex m x hx)]

theorem continuous_jet_eval {r m : ℕ} (I : Finset (Fin m)) (j : Fin (r + 1))
    (β : Fin (j : ℕ) → Fin m) : Continuous (fun w : Jet r m => w I j β) := by
  have : Continuous (fun w : ((I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) →
      (simplex m →ᵇ ℝ)) => w I j β) :=
    (continuous_apply β).comp ((continuous_apply j).comp (continuous_apply I))
  exact this

theorem coeff_extD {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (extD ω) I x = ∑ k : Fin m, ∑ J : Finset (Fin m),
      fderivWithin ℝ (coeff ω J) (simplex m) x (Pi.single k 1) *
        (formBasis m).repr (dx m k * formBasis m J) I := by
  simp only [coeff, extD, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

/-- A limit of jets of degree-`n` `Cʳ` forms is the jet of such a form `Ω0`; moreover the
coefficients of `d ω_k` converge pointwise on the simplex to those of `d Ω0`. -/
theorem jet_seq_limit {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) {ω : ℕ → Ω m}
    (hω : ∀ k, IsDeg n (ω k) ∧ IsCr r (ω k)) {w : ℕ → Jet r m × Jet r m}
    (hωw : ∀ k, jet r (ω k) = w k) {p : Jet r m × Jet r m} (hlim : Tendsto w atTop (𝓝 p)) :
    ∃ Ω0 : Ω m, (IsDeg n Ω0 ∧ IsCr r Ω0) ∧ jet r Ω0 = p ∧
      ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (extD (ω k)) I x) atTop
        (𝓝 (coeff (extD Ω0) I x)) := by
  have h1 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (ω k) I) j β) atTop (𝓝 (p.1 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_fst)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  have h2 : ∀ I (j : Fin (r + 1)) β,
      Tendsto (fun k => jetComp (coeff (extD (ω k)) I) j β) atTop (𝓝 (p.2 I j β)) := by
    intro I j β
    have := ((((continuous_jet_eval I j β).comp continuous_snd)).tendsto p).comp hlim
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, ← hωw k, jet]
  choose F hF hFj using fun I => jet_limit (fun k => ((hω k).2 I).1) (h1 I)
  choose G hG hGj using fun I => jet_limit (fun k => ((hω k).2 I).2) (h2 I)
  let Ω0 : Ω m := fun x => (formBasis m).equivFun.symm (fun I => F I x)
  have hcoeff : ∀ I, coeff Ω0 I = F I := by
    intro I; funext x
    show (formBasis m).repr ((formBasis m).equivFun.symm (fun I => F I x)) I = F I x
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let j0 : Fin (r + 1) := 0
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hj0 : (j0 : ℕ) = 0 := rfl
  have hpt0 : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (ω k) I x) atTop (𝓝 (F I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h1 I j0 β0)
    rw [← hFj I j0 β0, jetComp_zero (hF I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).1 hj0 β0 hx
  have hptG : ∀ I x (hx : x ∈ simplex m),
      Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (G I x)) := by
    intro I x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp (h2 I j0 β0)
    rw [← hGj I j0 β0, jetComp_zero (hG I) hj0 β0 hx] at this
    refine this.congr fun k => ?_
    exact jetComp_zero ((hω k).2 I).2 hj0 β0 hx
  let j1 : Fin (r + 1) := ⟨1, by omega⟩
  have hpt1 : ∀ J (q : Fin m) x (hx : x ∈ simplex m),
      Tendsto (fun k => fderivWithin ℝ (coeff (ω k) J) (simplex m) x (Pi.single q 1)) atTop
        (𝓝 (fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1))) := by
    intro J q x hx
    have := ((continuous_eval_const (⟨x, hx⟩ : ↥(simplex m))).tendsto _).comp
      (h1 J j1 (fun _ => q))
    rw [← hFj J j1 (fun _ => q)] at this
    have e1 : jetComp (F J) (j1 : ℕ) (fun _ => q) ⟨x, hx⟩ =
        fderivWithin ℝ (coeff Ω0 J) (simplex m) x (Pi.single q 1) := by
      rw [hcoeff J]; exact jetComp_one (hF J) hr (fun _ => q) hx
    rw [e1] at this
    refine this.congr fun k => ?_
    exact jetComp_one ((hω k).2 J).1 hr (fun _ => q) hx
  have hext : ∀ I, ∀ x ∈ simplex m, coeff (extD Ω0) I x = G I x := by
    intro I x hx
    have hA : Tendsto (fun k => coeff (extD (ω k)) I x) atTop (𝓝 (coeff (extD Ω0) I x)) := by
      simp only [coeff_extD]
      exact tendsto_finsetSum _ fun q _ => tendsto_finsetSum _ fun J _ =>
        (hpt1 J q x hx).mul_const _
    exact tendsto_nhds_unique hA (hptG I x hx)
  have hDeg : IsDeg n Ω0 := by
    intro x hx
    let W := (⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ))).map
      (formBasis m).equivFun.toLinearMap
    have hWc : IsClosed (W : Set (Finset (Fin m) → ℝ)) := W.closed_of_finiteDimensional
    have hT : Tendsto (fun k => (formBasis m).equivFun (ω k x)) atTop (𝓝 fun I => F I x) := by
      refine tendsto_pi_nhds.mpr fun I => (hpt0 I x hx).congr fun k => ?_
      rw [Module.Basis.equivFun_apply]; rfl
    have hmem : (fun I => F I x) ∈ W := hWc.mem_of_tendsto hT
      (Eventually.of_forall fun k => Submodule.mem_map_of_mem ((hω k).1 x hx))
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp hmem
    have : Ω0 x = v := by
      show (formBasis m).equivFun.symm (fun I => F I x) = v
      rw [← hve]; exact LinearEquiv.symm_apply_apply _ v
    rw [this]; exact hv
  have hCr : IsCr r Ω0 := fun I =>
    ⟨(hcoeff I).symm ▸ hF I, (hG I).congr fun x hx => hext I x hx⟩
  refine ⟨Ω0, ⟨hDeg, hCr⟩, ?_, fun I x hx => by rw [hext I x hx]; exact hptG I x hx⟩
  refine Prod.ext ?_ ?_
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff Ω0 I) k β) = p.1
    funext I j β
    rw [hcoeff I, hFj I j β]
  · show (fun I (k : Fin (r + 1)) β => jetComp (coeff (extD Ω0) I) k β) = p.2
    funext I j β
    rw [jetComp_congr (hext I) β, hGj I j β]

theorem jetImage_closed {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    IsClosed (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω}) := by
  refine IsSeqClosed.isClosed fun w p hw hlim => ?_
  choose ω hω hωw using hw
  obtain ⟨Ω0, h0, hj, -⟩ := jet_seq_limit hr n hω hωw hlim
  exact ⟨Ω0, h0, hj⟩

theorem jetClosedImage_closed {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    IsClosed (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω}) := by
  refine IsSeqClosed.isClosed fun w p hw hlim => ?_
  choose ω hω hωw using hw
  obtain ⟨Ω0, ⟨hD, hC⟩, hj, ht⟩ :=
    jet_seq_limit hr n (fun k => ⟨(hω k).1, (hω k).2.1⟩) hωw hlim
  refine ⟨Ω0, ⟨hD, hC, fun x hx => ?_⟩, hj⟩
  have h0 : ∀ I, coeff (extD Ω0) I x = 0 := by
    intro I
    refine tendsto_nhds_unique (ht I x hx) ?_
    have hz : ∀ k, coeff (extD (ω k)) I x = 0 := fun k => by
      simp only [coeff, (hω k).2.2 x hx, map_zero, Finsupp.zero_apply]
    simp only [hz]; exact tendsto_const_nhds
  refine (formBasis m).ext_elem fun I => ?_
  rw [map_zero, Finsupp.zero_apply]
  exact h0 I

end JetClosed

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} := by
  rw [crForms_coe hr n, (jetImage_closed hr n).closure_eq]

section ClosedSpan

variable {m r : ℕ}

theorem isClosedForm_add (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
    (h : IsClosedForm ω) (h' : IsClosedForm ω') : IsClosedForm (ω + ω') := fun x hx => by
  rw [extD_add hr hω hω' hx, h x hx, h' x hx, add_zero]

theorem isClosedForm_smul (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω)
    (h : IsClosedForm ω) : IsClosedForm (c • ω) := fun x hx => by
  rw [extD_smul hr c hω hx, h x hx, smul_zero]

theorem isClosedForm_zero : IsClosedForm (0 : Ω m) := by
  intro x _
  have h0 : ∀ J, coeff (0 : Ω m) J = fun _ => 0 := by intro J; funext x; simp [coeff]
  simp [extD, h0]

theorem span_jetClosed_eq (hr : 1 ≤ r) (n : ℕ) :
    ((Submodule.span ℝ (jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω}) :
      Submodule ℝ _) : Set (Jet r m × Jet r m)) =
      jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by
  refine le_antisymm (fun w hw => ?_) Submodule.subset_span
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero =>
    refine ⟨0, ⟨isDeg_zero, isCr_zero, isClosedForm_zero⟩, ?_⟩
    have := jet_smul (m := m) hr 0 (isCr_zero (m := m) (r := r))
    simpa using this
  | add a b _ _ ha hb =>
    obtain ⟨ω, ⟨h1, h2, h3⟩, rfl⟩ := ha
    obtain ⟨ω', ⟨h1', h2', h3'⟩, rfl⟩ := hb
    exact ⟨ω + ω', ⟨isDeg_add h1 h1', isCr_add hr h2 h2', isClosedForm_add hr h2 h2' h3 h3'⟩,
      jet_add hr h2 h2'⟩
  | smul c a _ ha =>
    obtain ⟨ω, ⟨h1, h2, h3⟩, rfl⟩ := ha
    exact ⟨c • ω, ⟨isDeg_smul c h1, isCr_smul hr c h2, isClosedForm_smul hr c h2 h3⟩,
      jet_smul hr c h2⟩

theorem crClosed_eq_image (hr : 1 ≤ r) (n : ℕ) :
    (CrClosed r m n : Set (Jet r m × Jet r m)) =
      jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by
  rw [CrClosed, Submodule.topologicalClosure_coe, span_jetClosed_eq hr n,
    (jetClosedImage_closed hr n).closure_eq]

end ClosedSpan

section Rep

variable {m r : ℕ}

end Rep

section Pull

variable {m r : ℕ}

end Pull

end IntLInfty.Kan.A83

open IntLInfty.Kan in
theorem solution {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} ∧
      (CrClosed r m n : Set (Jet r m × Jet r m)) =
        jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω} := by
  exact
      ⟨IntLInfty.Kan.A83.crForms_eq_image hr n, IntLInfty.Kan.A83.crClosed_eq_image hr n⟩
