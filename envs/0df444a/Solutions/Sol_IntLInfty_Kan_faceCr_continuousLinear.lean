-- Prove2me | solution 1 for IntLInfty.Kan.faceCr_continuousLinear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:02:23.120944+00:00
-- url     : https://prove2.me/submissions/d2bc1e79-ea9f-4e3c-94ec-2da3ae64870c

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

-- slice of scratch/probe/a83e3b53.lean (closure of the decls used below), unit FORMS2

set_option autoImplicit false

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

/-! Representative independence: the jet of a form only depends on its values on the simplex, and
it determines those values; hence `faceCr`, `faceCl`, `dCr` are computed by any representative. -/

variable {m r : ℕ}

/-- Two forms agree on the simplex. -/
def FormEqOn (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem coeff_eqOn {ω ω' : Ω m} (h : FormEqOn ω ω') (I : Finset (Fin m)) :
    Set.EqOn (coeff ω I) (coeff ω' I) (simplex m) := fun x hx => by
  simp only [coeff, h x hx]

theorem extD_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : FormEqOn (extD ω) (extD ω') := by
  intro x hx
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [fderivWithin_congr (coeff_eqOn h I) (coeff_eqOn h I hx)]

theorem jet_congr {ω ω' : Ω m} (h : FormEqOn ω ω') : jet r ω = jet r ω' := by
  have h1 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff ω I) k β = jetComp (coeff ω' I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn h I) β
  have h2 : ∀ I, ∀ k (β : Fin k → Fin m),
      jetComp (coeff (extD ω) I) k β = jetComp (coeff (extD ω') I) k β :=
    fun I _ β => jetComp_congr (coeff_eqOn (extD_congr h) I) β
  simp only [jet, h1, h2]

theorem formEqOn_of_jet {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
    (h : jet r ω = jet r ω') : FormEqOn ω ω' := by
  intro x hx
  refine (formBasis m).ext_elem fun I => ?_
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have e : (jet r ω).1 I j0 β0 = (jet r ω').1 I j0 β0 := by rw [h]
  simp only [jet] at e
  have e2 := congrArg (fun g : BoundedContinuousFunction (simplex m) ℝ => g ⟨x, hx⟩) e
  rw [jetComp_zero (hω I).1 hj0 β0 hx, jetComp_zero (hω' I).1 hj0 β0 hx] at e2
  exact e2

theorem vertex_mem (m : ℕ) (j : Fin (m + 1)) : vertex m j ∈ simplex m := by
  induction j using Fin.cases with
  | zero => exact ⟨fun _ => le_refl _, by simp [vertex]⟩
  | succ k =>
    simp only [vertex, Fin.cases_succ]
    refine ⟨fun a => ?_, ?_⟩
    · by_cases hak : a = k
      · subst hak; simp
      · simp [hak]
    · simp

theorem coface_eq (i : Fin (m + 2)) (x : Fin m → ℝ) :
    coface m i x = vertex (m + 1) (i.succAbove 0) + ∑ k, x k •
      (vertex (m + 1) (i.succAbove k.succ) - vertex (m + 1) (i.succAbove 0)) := by
  funext a
  simp [coface, cofaceLin, Matrix.mulVec, dotProduct, mul_comm]

theorem coface_mem (i : Fin (m + 2)) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    coface m i x ∈ simplex (m + 1) := by
  let w : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ w j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [w, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [w, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, w j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [w, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex (m + 1)).sum_mem h0 h1
    (z := fun j => vertex (m + 1) (i.succAbove j)) (fun j _ => vertex_mem _ _)
  convert hm using 1
  rw [coface_eq, Fin.sum_univ_succ]
  simp only [w, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

theorem pull_congr (i : Fin (m + 2)) {ω ω' : Ω (m + 1)} (h : FormEqOn ω ω') :
    FormEqOn (pull m i ω) (pull m i ω') := fun x hx => by
  simp only [pull]; rw [h _ (coface_mem i hx)]

theorem viaRep_spec {m' n : ℕ} {V : Submodule ℝ (Jet r m' × Jet r m')} {F : Ω m → Ω m'}
    (hF : ∀ ω ω' : Ω m, FormEqOn ω ω' → FormEqOn (F ω) (F ω')) {ω : Ω m} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hV : jet r (F ω) ∈ V) :
    (viaRep n V F (jet r ω) : Jet r m' × Jet r m') = jet r (F ω) := by
  have hex : ∃ ω' : Ω m, IsDeg n ω' ∧ IsCr r ω' ∧ jet r ω' = jet r ω ∧ jet r (F ω') ∈ V :=
    ⟨ω, hD, hC, rfl, hV⟩
  simp only [viaRep, dif_pos hex]
  exact jet_congr (hF _ _ (formEqOn_of_jet hex.choose_spec.2.1 hC hex.choose_spec.2.2.1))

theorem faceCr_spec {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrForms r (m + 1) n) (hV : jet r (pull m i ω) ∈ CrForms r m n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) :=
  viaRep_spec (fun _ _ h => pull_congr i h) hD hC hV

theorem faceCl_spec {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω)
    (hw : jet r ω ∈ CrClosed r (m + 1) n) (hV : jet r (pull m i ω) ∈ CrClosed r m n) :
    (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) :=
  viaRep_spec (fun _ _ h => pull_congr i h) hD hC hV

end Rep

section Pull

/-! Pullback along cofaces preserves degree and the `Cʳ` condition, and commutes with `d`. -/

variable {m r : ℕ}

theorem map_mem_exteriorPower {M N : Type} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (f : M →ₗ[ℝ] N) {n : ℕ} {a : ExteriorAlgebra ℝ M} (ha : a ∈ ⋀[ℝ]^n M) :
    ExteriorAlgebra.map f a ∈ ⋀[ℝ]^n N := by
  have h1 : (⋀[ℝ]^n M).map (ExteriorAlgebra.map f).toLinearMap ≤ ⋀[ℝ]^n N := by
    show Submodule.map _ (LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n) ≤
      LinearMap.range (ExteriorAlgebra.ι ℝ) ^ n
    rw [Submodule.map_pow]
    refine pow_le_pow_left' ?_ n
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, (ExteriorAlgebra.map_apply_ι f x).symm⟩
  exact h1 (Submodule.mem_map_of_mem ha)

theorem pull_isDeg {n : ℕ} (i : Fin (m + 2)) {ω : Ω (m + 1)} (h : IsDeg n ω) :
    IsDeg n (pull m i ω) := fun x hx =>
  map_mem_exteriorPower _ (h _ (coface_mem i hx))

theorem coeff_pull (i : Fin (m + 2)) (ω : Ω (m + 1)) (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pull m i ω) J x = ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J := by
  simp only [coeff, pull]
  conv_lhs => rw [← (formBasis (m + 1)).sum_repr (ω (coface m i x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem coface_eq_clm (i : Fin (m + 2)) : coface m i =
    fun x => vertex (m + 1) (i.succAbove 0) + LinearMap.toContinuousLinearMap (cofaceLin m i) x :=
  rfl

theorem hasFDerivAt_coface (i : Fin (m + 2)) (x : Fin m → ℝ) :
    HasFDerivAt (coface m i) (LinearMap.toContinuousLinearMap (cofaceLin m i)) x := by
  rw [coface_eq_clm]
  exact (LinearMap.toContinuousLinearMap (cofaceLin m i)).hasFDerivAt.const_add _

theorem contDiff_coface {n : WithTop ℕ∞} (i : Fin (m + 2)) : ContDiff ℝ n (coface m i) := by
  rw [coface_eq_clm]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

theorem contDiffOn_coeff_pull (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pull m i ω) J) (simplex m) := by
  have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) *
      (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J :=
    funext (coeff_pull i ω J)
  rw [e]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_coface i).contDiffOn (fun x hx => coface_mem i hx)).mul contDiffOn_const

theorem dualMap_proj {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (a : Fin m') :
    L.dualMap (LinearMap.proj a) =
      ∑ k, (L (Pi.single k 1) a) • (LinearMap.proj k : (Fin m → ℝ) →ₗ[ℝ] ℝ) := by
  ext j
  simp [LinearMap.dualMap_apply, Pi.single_apply]

theorem linear_expand {m' : ℕ} {A : Type} [AddCommGroup A] [Module ℝ A]
    (T : (Fin m' → ℝ) →ₗ[ℝ] A) (v : Fin m' → ℝ) : T v = ∑ a, v a • T (Pi.single a 1) := by
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin m')).sum_repr v]
  simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr]

theorem wedge_natural {m' : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ))) :
    ExteriorAlgebra.map L.dualMap (∑ a, dx m' a * T (Pi.single a 1)) =
      ∑ k, dx m k * ExteriorAlgebra.map L.dualMap (T (L (Pi.single k 1))) := by
  simp only [map_sum, map_mul, dx, ExteriorAlgebra.map_apply_ι, dualMap_proj, map_smul,
    Finset.sum_mul, smul_mul_assoc]
  conv_rhs => enter [2, k]; rw [linear_expand T (L (Pi.single k 1))]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  exact Finset.sum_comm

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pc (i : Fin (m + 2)) (I : Finset (Fin (m + 1))) (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map (cofaceLin m i).dualMap (formBasis (m + 1) I)) J

theorem extD_pull (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex (m + 1))) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pull m i ω) x = pull m i (extD ω) x := by
  have hy : coface m i x ∈ simplex (m + 1) := coface_mem i hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)) (simplex (m + 1))
      (coface m i x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pull m i ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)
        (cofaceLin m i (Pi.single k 1)) * pc i I J := by
    intro J k
    have e : coeff (pull m i ω) J = fun x => ∑ I, coeff ω I (coface m i x) * pc i I J :=
      funext (coeff_pull i ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (coface m i x) * pc i I J)
        (∑ I, (pc i I J) • ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x)).comp
          (LinearMap.toContinuousLinearMap (cofaceLin m i)))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_coface i x).hasFDerivWithinAt
        (fun z hz => coface_mem i hz)).mul_const (pc i I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin (m + 1) → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin (m + 1) → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) :
      (Fin (m + 1) → ℝ) →L[ℝ] ℝ) : (Fin (m + 1) → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis (m + 1) I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex (m + 1)) (coface m i x) v •
      formBasis (m + 1) I := by
    intro v; simp [T]
  have hR : pull m i (extD ω) x = ExteriorAlgebra.map (cofaceLin m i).dualMap
      (∑ a, dx (m + 1) a * T (Pi.single a 1)) := by
    simp only [hT]; rfl
  rw [hR, wedge_natural]
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hT]
  simp only [hpd, map_sum, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (formBasis m).sum_repr _

theorem pull_isCr (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω) :
    IsCr r (pull m i ω) := fun J =>
  ⟨contDiffOn_coeff_pull i (fun I => (hC I).1) J,
    (contDiffOn_coeff_pull i (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pull m i ω) x) J = (formBasis m).repr (pull m i (extD ω) x) J
      rw [extD_pull hr i (fun I => (hC I).1) hx]⟩

theorem pull_isClosedForm (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω)
    (h : IsClosedForm ω) : IsClosedForm (pull m i ω) := fun x hx => by
  rw [extD_pull hr i (fun I => (hC I).1) hx]
  show ExteriorAlgebra.map _ (extD ω (coface m i x)) = 0
  rw [h _ (coface_mem i hx), map_zero]

theorem faceCr_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hw : jet r ω ∈ CrForms r (m + 1) n) :
    (faceCr r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCr_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrForms r m n : Set (Jet r m × Jet r m))
  rw [crForms_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC⟩, rfl⟩

theorem faceCl_eq {n : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hD : IsDeg n ω)
    (hC : IsCr r ω) (hcl : IsClosedForm ω) (hw : jet r ω ∈ CrClosed r (m + 1) n) :
    (faceCl r m n i ⟨jet r ω, hw⟩ : Jet r m × Jet r m) = jet r (pull m i ω) := by
  refine faceCl_spec i hD hC hw ?_
  show jet r (pull m i ω) ∈ (CrClosed r m n : Set (Jet r m × Jet r m))
  rw [crClosed_eq_image hr n]
  exact ⟨_, ⟨pull_isDeg i hD, pull_isCr hr i hC, pull_isClosedForm hr i hC hcl⟩, rfl⟩

end Pull

section PullAff

/-! Pullback along an arbitrary affine map `x ↦ b + L x` sending `Δᵐ` into `Δᵐ'` (the retractions
used by the horn-extension operator of Lemma 5.9 are of this kind). -/

variable {m m' r : ℕ}

/-- Pullback of forms along the affine map `x ↦ b + L x`. -/
noncomputable def pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m') : Ω m :=
  fun x => ExteriorAlgebra.map L.dualMap (ω (b + L x))

/-- The coefficients of the pulled-back basis forms. -/
noncomputable def pcA (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (I : Finset (Fin m'))
    (J : Finset (Fin m)) : ℝ :=
  (formBasis m).repr (ExteriorAlgebra.map L.dualMap (formBasis m' I)) J

theorem coeff_pullA (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω : Ω m')
    (J : Finset (Fin m)) (x : Fin m → ℝ) :
    coeff (pullA b L ω) J x = ∑ I, coeff ω I (b + L x) * pcA L I J := by
  simp only [coeff, pullA, pcA]
  conv_lhs => rw [← (formBasis m').sum_repr (ω (b + L x))]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem hasFDerivAt_aff (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (x : Fin m → ℝ) :
    HasFDerivAt (fun x => b + L x) (LinearMap.toContinuousLinearMap L) x :=
  (LinearMap.toContinuousLinearMap L).hasFDerivAt.const_add _

theorem contDiff_aff {n : WithTop ℕ∞} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) :
    ContDiff ℝ n (fun x => b + L x) :=
  contDiff_const.add (LinearMap.toContinuousLinearMap L).contDiff

theorem contDiffOn_coeff_pullA {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) (J : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff (pullA b L ω) J) (simplex m) := by
  rw [show coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J from
    funext (coeff_pullA b L ω J)]
  exact ContDiffOn.sum fun I _ =>
    ((h I).comp (contDiff_aff b L).contDiffOn (fun x hx => hA x hx)).mul contDiffOn_const

theorem extD_pullA (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'}
    (hC : ∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (pullA b L ω) x = pullA b L (extD ω) x := by
  have hy : b + L x ∈ simplex m' := hA x hx
  have hd : ∀ I, HasFDerivWithinAt (coeff ω I)
      (fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)) (simplex m') (b + L x) := fun I =>
    (((hC I).differentiableOn (by exact_mod_cast (show r ≠ 0 by omega))) _ hy).hasFDerivWithinAt
  have hpd : ∀ J (k : Fin m), fderivWithin ℝ (coeff (pullA b L ω) J) (simplex m) x (Pi.single k 1) =
      ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) (L (Pi.single k 1)) * pcA L I J := by
    intro J k
    have e : coeff (pullA b L ω) J = fun x => ∑ I, coeff ω I (b + L x) * pcA L I J :=
      funext (coeff_pullA b L ω J)
    have hH : HasFDerivWithinAt (fun x => ∑ I, coeff ω I (b + L x) * pcA L I J)
        (∑ I, (pcA L I J) • ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x)).comp
          (LinearMap.toContinuousLinearMap L))) (simplex m) x := by
      refine HasFDerivWithinAt.fun_sum (u := Finset.univ) fun I _ => ?_
      exact ((hd I).comp x (hasFDerivAt_aff b L x).hasFDerivWithinAt
        (fun z hz => hA z hz)).mul_const (pcA L I J)
    rw [e, hH.fderivWithin (uniqueDiffOn_simplex m x hx)]
    simp [mul_comm]
  let T : (Fin m' → ℝ) →ₗ[ℝ] ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m' → ℝ)) :=
    ∑ I, ((fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) :
      (Fin m' → ℝ) →L[ℝ] ℝ) : (Fin m' → ℝ) →ₗ[ℝ] ℝ).smulRight (formBasis m' I)
  have hT : ∀ v, T v = ∑ I, fderivWithin ℝ (coeff ω I) (simplex m') (b + L x) v •
      formBasis m' I := by
    intro v; simp [T]
  have hR : pullA b L (extD ω) x = ExteriorAlgebra.map L.dualMap
      (∑ a, dx m' a * T (Pi.single a 1)) := by
    simp only [hT]; rfl
  rw [hR, wedge_natural]
  simp only [extD]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [hT]
  simp only [hpd, map_sum, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  exact (formBasis m).sum_repr _

theorem pullA_isCr (hr : 1 ≤ r) {b : Fin m' → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)}
    (hA : ∀ x ∈ simplex m, b + L x ∈ simplex m') {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullA b L ω) := fun J =>
  ⟨contDiffOn_coeff_pullA hA (fun I => (hC I).1) J,
    (contDiffOn_coeff_pullA hA (fun I => (hC I).2) J).congr fun x hx => by
      show (formBasis m).repr (extD (pullA b L ω) x) J = (formBasis m).repr (pullA b L (extD ω) x) J
      rw [extD_pullA hr hA (fun I => (hC I).1) hx]⟩

/-- Pullback is linear (pointwise, everywhere). -/
theorem pullA_add (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (ω ω' : Ω m') :
    pullA b L (ω + ω') = pullA b L ω + pullA b L ω' := by
  funext x; simp [pullA, map_add]

theorem pullA_smul (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)) (c : ℝ) (ω : Ω m') :
    pullA b L (c • ω) = c • pullA b L ω := by
  funext x; simp [pullA, map_smul]

/-- Functoriality: pulling back along `A ∘ B` is pulling back along `A`, then along `B`. -/
theorem pullA_comp {m'' : ℕ} (b : Fin m' → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ))
    (b' : Fin m → ℝ) (L' : (Fin m'' → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (ω : Ω m') :
    pullA b' L' (pullA b L ω) = pullA (b + L b') (L ∘ₗ L') ω := by
  funext x
  simp only [pullA, LinearMap.comp_apply, map_add, add_assoc]
  rw [← LinearMap.dualMap_comp_dualMap, ← ExteriorAlgebra.map_comp_map]
  rfl

end PullAff

section PullS

/-! Simplicial pullbacks: the affine map `Δᵐ → Δᵐ'` sending the vertex `v_l` to `v_{θ l}` for any
`θ : Fin (m+1) → Fin (m'+1)` (cofaces, codegeneracies and the horn retractions), and functoriality. -/

variable {m m' r : ℕ}

/-- The linear part of the affine map with vertex images `w`. -/
noncomputable def affL (w : Fin (m + 1) → (Fin m' → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ) :=
  (Matrix.of fun (a : Fin m') (k : Fin m) => (w k.succ - w 0) a).mulVecLin

theorem affL_apply (w : Fin (m + 1) → (Fin m' → ℝ)) (x : Fin m → ℝ) :
    affL w x = ∑ k, x k • (w k.succ - w 0) := by
  funext a
  simp [affL, Matrix.mulVec, dotProduct, mul_comm]

theorem aff_vertex (w : Fin (m + 1) → (Fin m' → ℝ)) (l : Fin (m + 1)) :
    w 0 + affL w (vertex m l) = w l := by
  induction l using Fin.cases with
  | zero => simp [vertex]
  | succ k =>
    rw [affL_apply]
    simp [vertex, Pi.single_apply]

theorem aff_mem {w : Fin (m + 1) → (Fin m' → ℝ)} (hw : ∀ l, w l ∈ simplex m') :
    ∀ x ∈ simplex m, w 0 + affL w x ∈ simplex m' := by
  intro x hx
  let c : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ k, x k) x
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))), 0 ≤ c j := by
    intro j _
    induction j using Fin.cases with
    | zero => simp only [c, Fin.cons_zero]; linarith [hx.2]
    | succ k => simp only [c, Fin.cons_succ]; exact hx.1 k
  have h1 : ∑ j, c j = 1 := by
    rw [Fin.sum_univ_succ]; simp only [c, Fin.cons_zero, Fin.cons_succ]; ring
  have hm := (convex_simplex m').sum_mem h0 h1 (z := w) (fun j _ => hw j)
  convert hm using 1
  rw [affL_apply, Fin.sum_univ_succ]
  simp only [c, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul,
    one_smul, ← Finset.sum_smul]
  abel

/-- An affine map is determined by its vertex images. -/
theorem aff_ext {w : Fin (m + 1) → (Fin m' → ℝ)} {b : Fin m' → ℝ}
    {L : (Fin m → ℝ) →ₗ[ℝ] (Fin m' → ℝ)} (h : ∀ l, b + L (vertex m l) = w l) :
    b = w 0 ∧ L = affL w := by
  have hb : b = w 0 := by
    have := h 0
    simpa [vertex] using this
  refine ⟨hb, LinearMap.ext fun x => ?_⟩
  rw [linear_expand L x, linear_expand (affL w) x]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have h1 := h a.succ
  have h2 := aff_vertex w a.succ
  simp only [vertex, Fin.cases_succ] at h1 h2
  rw [hb] at h1
  exact add_left_cancel (h1.trans h2.symm)

/-- Pullback along the simplicial affine map with vertex map `θ`. -/
noncomputable def pullS (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') : Ω m :=
  pullA (vertex m' (θ 0)) (affL fun l => vertex m' (θ l)) ω

theorem pull_eq_pullS (i : Fin (m + 2)) (ω : Ω (m + 1)) : pull m i ω = pullS i.succAbove ω := rfl

theorem pullS_mem (θ : Fin (m + 1) → Fin (m' + 1)) :
    ∀ x ∈ simplex m, vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) x ∈ simplex m' :=
  aff_mem (w := fun l => vertex m' (θ l)) fun l => vertex_mem _ _

theorem pullS_comp {m'' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
    (ω : Ω m') : pullS θ' (pullS θ ω) = pullS (θ ∘ θ') ω := by
  simp only [pullS]
  rw [pullA_comp]
  obtain ⟨h1, h2⟩ := aff_ext (w := fun l => vertex m' (θ (θ' l)))
    (b := vertex m' (θ 0) + (affL fun l => vertex m' (θ l)) (vertex m (θ' 0)))
    (L := (affL fun l => vertex m' (θ l)) ∘ₗ (affL fun l => vertex m (θ' l))) (fun l => by
      rw [LinearMap.comp_apply, add_assoc, ← map_add,
        aff_vertex (fun l => vertex m (θ' l)) l, aff_vertex (fun l => vertex m' (θ l)) (θ' l)])
  rw [h1, h2]
  rfl

theorem pullS_isCr (hr : 1 ≤ r) (θ : Fin (m + 1) → Fin (m' + 1)) {ω : Ω m'} (hC : IsCr r ω) :
    IsCr r (pullS θ ω) := pullA_isCr hr (pullS_mem θ) hC

end PullS

section HornExt

/-! Horn filling for forms at the level of representatives (Lemma 5.9, surjectivity): the classical
inductive extension, correcting face by face with pullbacks along the retraction `retr i j` of
`Δᵐ⁺¹` onto its `i`-th face that moves the vertex `i` to the vertex `j`. -/

variable {m r : ℕ}

theorem pullS_add' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m') :
    pullS θ (ω + ω') = pullS θ ω + pullS θ ω' := pullA_add _ _ _ _

end HornExt

section HornJet

/-! Lemma 5.9 surjectivity at the jet level: a compatible tuple of jets (codim-2 identities only)
lifts to a strongly compatible tuple of representatives, which then fills. -/

variable {m r : ℕ}

/-- Cosimplicial identity `δ_a ∘ δ_b = δ_{b+1} ∘ δ_a` for `a ≤ b`. -/
theorem succAbove_succAbove_le {a b : Fin (m + 1)} (hab : a ≤ b) (l : Fin m) :
    a.castSucc.succAbove (b.succAbove l) = b.succ.succAbove (a.succAbove l) := by
  rw [Fin.le_def] at hab
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> (try simp only [Fin.val_castSucc, Fin.val_succ, not_lt] at *) <;> omega

end HornJet

section Fold

/-! The horn-filling operator as an explicit fold (linear in the tuple, respects `FormEqOn`):
the input to the closed-graph argument for a continuous linear section. -/

variable {m r : ℕ}

theorem pullS_smul' {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m') :
    pullS θ (c • ω) = c • pullS θ ω := pullA_smul _ _ _ _

end Fold

section ClosedGraph

/-! Continuity of the face maps and of the horn section by the closed graph theorem: limits in the
jet space control the coefficients pointwise (order-0 jet components), and pullbacks / folds
preserve pointwise convergence of coefficients. -/

variable {m r : ℕ}

/-- Pointwise convergence of all coefficients on the simplex. -/
def CoeffTendsto (ωk : ℕ → Ω m) (ω : Ω m) : Prop :=
  ∀ I, ∀ x ∈ simplex m, Tendsto (fun k => coeff (ωk k) I x) atTop (𝓝 (coeff ω I x))

theorem coeffTendsto_pullS {m' : ℕ} (θ : Fin (m + 1) → Fin (m' + 1)) {ωk : ℕ → Ω m'}
    {ω : Ω m'} (h : CoeffTendsto ωk ω) :
    CoeffTendsto (fun k => pullS θ (ωk k)) (pullS θ ω) := by
  intro J x hx
  simp only [pullS, coeff_pullA]
  exact tendsto_finset_sum _ fun I _ => (h I _ (pullS_mem θ x hx)).mul_const _

theorem coeffTendsto_of_jet {ωk : ℕ → Ω m} {ω : Ω m} (hk : ∀ k, IsCr r (ωk k)) (hω : IsCr r ω)
    (h : Tendsto (fun k => jet r (ωk k)) atTop (𝓝 (jet r ω))) : CoeffTendsto ωk ω := by
  intro I x hx
  let j0 : Fin (r + 1) := 0
  have hj0 : (j0 : ℕ) = 0 := rfl
  have β0 : Fin (j0 : ℕ) → Fin m := fun l => absurd l.isLt (by simp [j0])
  have hc : Continuous (fun w : Jet r m × Jet r m => w.1 I j0 β0 ⟨x, hx⟩) :=
    (continuous_eval_const _).comp
      ((continuous_jet_eval I j0 β0).comp continuous_fst)
  have t := (hc.tendsto _).comp h
  have e1 : (jet r ω).1 I j0 β0 ⟨x, hx⟩ = coeff ω I x := jetComp_zero (hω I).1 hj0 β0 hx
  rw [Function.comp_def, e1] at t
  exact t.congr fun k => jetComp_zero ((hk k) I).1 hj0 β0 hx

theorem coeffTendsto_unique {ωk : ℕ → Ω m} {a b : Ω m} (h1 : CoeffTendsto ωk a)
    (h2 : CoeffTendsto ωk b) : FormEqOn a b := fun x hx =>
  (formBasis m).ext_elem fun I => tendsto_nhds_unique (h1 I x hx) (h2 I x hx)

theorem exists_rep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω) ∧ jet r ω = w := by
  have := w.2
  rw [← SetLike.mem_coe, crForms_eq_image hr n] at this
  exact this

theorem exists_rep_cl (hr : 1 ≤ r) {n : ℕ} (w : CrClosed r m n) :
    ∃ ω : Ω m, (IsDeg n ω ∧ IsCr r ω ∧ IsClosedForm ω) ∧ jet r ω = w := by
  have := w.2
  rw [← SetLike.mem_coe, crClosed_eq_image hr n] at this
  exact this

open BoundedContinuousFunction in
theorem jet_complete (r m : ℕ) : CompleteSpace (Jet r m × Jet r m) := by
  have : CompleteSpace (Jet r m) := inferInstanceAs (CompleteSpace ((I : Finset (Fin m)) →
    (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))
  infer_instance

theorem crForms_complete (r m n : ℕ) : CompleteSpace (CrForms r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem crClosed_complete (r m n : ℕ) : CompleteSpace (CrClosed r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem faceCr_val (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (h : jet r ω = w) :
    (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) := by
  obtain ⟨w, hw⟩ := w
  simp only at h
  subst h
  exact faceCr_eq hr i hD hC hw

theorem faceCl_val (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrClosed r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (hK : IsClosedForm ω) (h : jet r ω = w) :
    (faceCl r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) := by
  obtain ⟨w, hw⟩ := w
  simp only at h
  subst h
  exact faceCl_eq hr i hD hC hK hw

/-- The face map `dᵢ` on `Ωⁿ_{Cʳ}` as a linear map. -/
noncomputable def faceLin (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    CrForms r (m + 1) n →ₗ[ℝ] CrForms r m n where
  toFun := faceCr r m n i
  map_add' w w' := by
    obtain ⟨ω, hω, h⟩ := exists_rep hr w
    obtain ⟨ω', hω', h'⟩ := exists_rep hr w'
    apply Subtype.ext
    rw [Submodule.coe_add, faceCr_val hr i (w + w') (isDeg_add hω.1 hω'.1) (isCr_add hr hω.2 hω'.2)
      (by rw [jet_add hr hω.2 hω'.2, h, h']; rfl), faceCr_val hr i w hω.1 hω.2 h,
      faceCr_val hr i w' hω'.1 hω'.2 h', pull_eq_pullS, pull_eq_pullS, pull_eq_pullS, pullS_add',
      jet_add hr (pullS_isCr hr _ hω.2) (pullS_isCr hr _ hω'.2)]
  map_smul' c w := by
    obtain ⟨ω, hω, h⟩ := exists_rep hr w
    apply Subtype.ext
    rw [Submodule.coe_smul, faceCr_val hr i (c • w) (isDeg_smul c hω.1) (isCr_smul hr c hω.2)
      (by rw [jet_smul hr c hω.2, h]; rfl), faceCr_val hr i w hω.1 hω.2 h, pull_eq_pullS,
      pull_eq_pullS, pullS_smul', jet_smul hr c (pullS_isCr hr _ hω.2)]
    rfl

theorem faceLin_continuous (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    Continuous (faceLin (r := r) hr n i) := by
  haveI := crForms_complete r (m + 1) n
  haveI := crForms_complete r m n
  refine (faceLin hr n i).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  choose ωk hωk hk using fun k => exists_rep hr (u k)
  obtain ⟨ω, hω, hw⟩ := exists_rep hr w
  obtain ⟨ωz, hωz, hzj⟩ := exists_rep hr z
  have hface : ∀ k, (faceLin hr n i (u k) : Jet r m × Jet r m) = jet r (pull m i (ωk k)) :=
    fun k => faceCr_val hr i (u k) (hωk k).1 (hωk k).2 (hk k)
  have t1 : CoeffTendsto (fun k => pull m i (ωk k)) ωz := by
    refine coeffTendsto_of_jet (fun k => pull_isCr hr i (hωk k).2) hωz.2 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this.congr fun k => hface k
  have t2 : CoeffTendsto (fun k => pull m i (ωk k)) (pull m i ω) := by
    refine coeffTendsto_pullS i.succAbove (coeffTendsto_of_jet (fun k => (hωk k).2) hω.2 ?_)
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [hw]
    exact this.congr fun k => (hk k).symm
  apply Subtype.ext
  show (z : Jet r m × Jet r m) = faceCr r m n i w
  rw [faceCr_val hr i w hω.1 hω.2 hw, ← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

end ClosedGraph

section HornSection

/-! The continuous linear horn section `E` (fold of retraction pullbacks on representatives),
the simplicial identities for `faceCr`, and Lemma 5.9 for `Ωⁿ_{Cʳ}`. -/

variable {m r : ℕ}

/-- Simplicial identity `dₐ d_{b+1} = d_b dₐ` (`a ≤ b`) for `faceCr`. -/
theorem faceCr_faceCr (hr : 1 ≤ r) {n : ℕ} {a b : Fin (m + 2)} (hab : a ≤ b)
    (w : CrForms r (m + 2) n) :
    faceCr r m n a (faceCr r (m + 1) n b.succ w) = faceCr r m n b (faceCr r (m + 1) n a.castSucc w) := by
  obtain ⟨ω, hω, h⟩ := exists_rep hr w
  apply Subtype.ext
  rw [faceCr_val hr a _ (pull_isDeg _ hω.1) (pull_isCr hr _ hω.2)
      (faceCr_val hr b.succ w hω.1 hω.2 h).symm,
    faceCr_val hr b _ (pull_isDeg _ hω.1) (pull_isCr hr _ hω.2)
      (faceCr_val hr a.castSucc w hω.1 hω.2 h).symm]
  simp only [pull_eq_pullS, pullS_comp]
  rw [show b.succ.succAbove ∘ a.succAbove = a.castSucc.succAbove ∘ b.succAbove from
    funext fun l => (succAbove_succAbove_le hab l).symm]

end HornSection

section Lemma59

/-! Lemma 5.9 for `Ωⁿ_{Cʳ}(Δ^•)`: horn sets are closed complemented subspaces (the range of the
continuous projection `hornMap ∘ E`), and `hornMap` is a surjective submersion with the affine
  right inverse `y ↦ x + E (y - hornMap x)`. -/

variable {m r : ℕ}

end Lemma59

section Lemma59Closed

/-! Lemma 5.9 for closed forms `Ωⁿ_closed(Δ^•)`: same argument with closed representatives. -/

variable {m r : ℕ}

noncomputable def faceLinCl (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    CrClosed r (m + 1) n →ₗ[ℝ] CrClosed r m n where
  toFun := faceCl r m n i
  map_add' w w' := by
    obtain ⟨ω, hω, h⟩ := exists_rep_cl hr w
    obtain ⟨ω', hω', h'⟩ := exists_rep_cl hr w'
    apply Subtype.ext
    rw [Submodule.coe_add, faceCl_val hr i (w + w') (isDeg_add hω.1 hω'.1)
      (isCr_add hr hω.2.1 hω'.2.1) (isClosedForm_add hr hω.2.1 hω'.2.1 hω.2.2 hω'.2.2)
      (by rw [jet_add hr hω.2.1 hω'.2.1, h, h']; rfl), faceCl_val hr i w hω.1 hω.2.1 hω.2.2 h,
      faceCl_val hr i w' hω'.1 hω'.2.1 hω'.2.2 h', pull_eq_pullS, pull_eq_pullS, pull_eq_pullS,
      pullS_add', jet_add hr (pullS_isCr hr _ hω.2.1) (pullS_isCr hr _ hω'.2.1)]
  map_smul' c w := by
    obtain ⟨ω, hω, h⟩ := exists_rep_cl hr w
    apply Subtype.ext
    rw [Submodule.coe_smul, faceCl_val hr i (c • w) (isDeg_smul c hω.1) (isCr_smul hr c hω.2.1)
      (isClosedForm_smul hr c hω.2.1 hω.2.2)
      (by rw [jet_smul hr c hω.2.1, h]; rfl), faceCl_val hr i w hω.1 hω.2.1 hω.2.2 h,
      pull_eq_pullS, pull_eq_pullS, pullS_smul', jet_smul hr c (pullS_isCr hr _ hω.2.1)]
    rfl

theorem faceLinCl_continuous (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    Continuous (faceLinCl (r := r) hr n i) := by
  haveI := crClosed_complete r (m + 1) n
  haveI := crClosed_complete r m n
  refine (faceLinCl hr n i).continuous_of_seq_closed_graph fun u w z hu hz => ?_
  choose ωk hωk hk using fun k => exists_rep_cl hr (u k)
  obtain ⟨ω, hω, hw⟩ := exists_rep_cl hr w
  obtain ⟨ωz, hωz, hzj⟩ := exists_rep_cl hr z
  have hface : ∀ k, (faceLinCl hr n i (u k) : Jet r m × Jet r m) = jet r (pull m i (ωk k)) :=
    fun k => faceCl_val hr i (u k) (hωk k).1 (hωk k).2.1 (hωk k).2.2 (hk k)
  have t1 : CoeffTendsto (fun k => pull m i (ωk k)) ωz := by
    refine coeffTendsto_of_jet (fun k => pull_isCr hr i (hωk k).2.1) hωz.2.1 ?_
    have := (continuous_subtype_val.tendsto z).comp hz
    rw [hzj]
    exact this.congr fun k => hface k
  have t2 : CoeffTendsto (fun k => pull m i (ωk k)) (pull m i ω) := by
    refine coeffTendsto_pullS i.succAbove (coeffTendsto_of_jet (fun k => (hωk k).2.1) hω.2.1 ?_)
    have := (continuous_subtype_val.tendsto w).comp hu
    rw [hw]
    exact this.congr fun k => (hk k).symm
  apply Subtype.ext
  show (z : Jet r m × Jet r m) = faceCl r m n i w
  rw [faceCl_val hr i w hω.1 hω.2.1 hω.2.2 hw, ← hzj]
  exact jet_congr (coeffTendsto_unique t1 t2)

end Lemma59Closed

end IntLInfty.Kan.A83

open IntLInfty.Kan in
theorem solution (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (∀ (m : ℕ) (i : Fin (m + 2)),
      ∃ F : CrForms r (m + 1) n →L[ℝ] CrForms r m n, ∀ w, F w = faceCr r m n i w) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)),
      ∃ F : CrClosed r (m + 1) n →L[ℝ] CrClosed r m n, ∀ w, F w = faceCl r m n i w) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)) (w : CrForms r (m + 1) n) (ω : Ω (m + 1)),
      IsDeg n ω → IsCr r ω → jet r ω = w →
        (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ (m : ℕ) (i : Fin (m + 2)) (w : CrClosed r (m + 1) n) (ω : Ω (m + 1)),
      IsDeg n ω → IsCr r ω → IsClosedForm ω → jet r ω = w →
        (faceCl r m n i w : Jet r m × Jet r m) = jet r (pull m i ω)) ∧
    (∀ (m : ℕ) (a b : Fin (m + 2)), a ≤ b → ∀ w : CrForms r (m + 2) n,
      faceCr r m n a (faceCr r (m + 1) n b.succ w) =
        faceCr r m n b (faceCr r (m + 1) n a.castSucc w)) := by
  exact
      ⟨fun _ i => ⟨⟨A83.faceLin hr n i, A83.faceLin_continuous hr n i⟩, fun _ => rfl⟩,
       fun _ i => ⟨⟨A83.faceLinCl hr n i, A83.faceLinCl_continuous hr n i⟩, fun _ => rfl⟩,
       fun _ i w _ hD hC h => A83.faceCr_val hr i w hD hC h,
       fun _ i w _ hD hC hK h => A83.faceCl_val hr i w hD hC hK h,
       fun _ _ _ hab w => A83.faceCr_faceCr hr hab w⟩
