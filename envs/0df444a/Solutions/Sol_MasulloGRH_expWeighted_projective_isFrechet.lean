-- Prove2me | solution 1 for MasulloGRH.expWeighted_projective_isFrechet
-- status  : ACCEPTED   (prove)
-- author  : @kirisame
-- created : 2026-11-21T18:59:50.657066+00:00
-- url     : https://prove2.me/submissions/033689aa-7e66-48c5-8b39-c6a885cf315b

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel

set_option autoImplicit false

universe u

namespace MasulloGRHWFAux

open MasulloGRH Topology Filter Set

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

abbrev XT (m n : ℕ) := (Fin m → ℝ) × (Fin n → ℝ)
abbrev QQ (m n r s : ℕ) (d : Fin s → ℕ) :=
  (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ))
abbrev ES (m n r s : ℕ) (d : Fin s → ℕ) := ElemSchwartz m n r s d

lemma rd_zero : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  have h0 : ∀ a b, elemLift (0 : ElemGroup m n r s d → ℂ) a b = 0 := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact contDiff_const, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  rw [h0]
  simp

lemma rd_add {f g : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) (hg : IsRapidDecay g) :
    IsRapidDecay (f + g) := by
  have h0 : ∀ a b, elemLift (f + g) a b = elemLift f a b + elemLift g a b := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).add (hg.1 a b), fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  obtain ⟨C2, h2⟩ := hg.2 i j k
  refine ⟨C1 + C2, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_add_apply ((hf.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hg.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))]
  have := norm_add_le (iteratedFDeriv ℝ k (elemLift f a b) xt) (iteratedFDeriv ℝ k (elemLift g a b) xt)
  have hp : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt + iteratedFDeriv ℝ k (elemLift g a b) xt‖
      ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ + ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) :=
        mul_le_mul_of_nonneg_left this hp
    _ = ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖ := by ring
    _ ≤ C1 + C2 := add_le_add (h1 a b xt) (h2 a b xt)

lemma rd_smul (c : ℂ) {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) :
    IsRapidDecay (c • f) := by
  have h0 : ∀ a b, elemLift (c • f) a b = c • elemLift f a b := fun _ _ => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  refine ⟨‖c‖ * C1, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_const_smul_apply ((hf.1 a b).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖c‖ * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖)
      = ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) := by ring
    _ ≤ ‖c‖ * C1 := mul_le_mul_of_nonneg_left (h1 a b xt) (norm_nonneg c)

lemma rd (g : ES m n r s d) : IsRapidDecay g.toFun := by
  have h := g.2
  change g.1 ∈ Submodule.span ℂ {g | IsRapidDecay g} at h
  show IsRapidDecay g.1
  exact Submodule.span_induction (p := fun x _ => IsRapidDecay x) (fun x hx => hx) rd_zero
    (fun x y _ _ hx hy => rd_add hx hy) (fun c x _ hx => rd_smul c hx) h

lemma lift_smooth (g : ES m n r s d) (a b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift g.toFun a b) := (rd g).1 a b

lemma lift_add (f g : ES m n r s d) (a b) :
    elemLift (f + g).toFun a b = elemLift f.toFun a b + elemLift g.toFun a b := rfl

lemma lift_smul (c : ℂ) (g : ES m n r s d) (a b) :
    elemLift (c • g).toFun a b = c • elemLift g.toFun a b := rfl

/-- the weighted derivative (as in the topology instance) -/
def wtd (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) :
    ES m n r s d →ₗ[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ where
  toFun g := (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
    iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2
  map_add' f g := by
    rw [lift_add, iteratedFDeriv_add_apply ((lift_smooth f _ _).contDiffAt.of_le
      (by exact_mod_cast le_top)) ((lift_smooth g _ _).contDiffAt.of_le (by exact_mod_cast le_top)),
      smul_add]
  map_smul' c g := by
    simp only [RingHom.id_apply]
    rw [lift_smul, iteratedFDeriv_const_smul_apply ((lift_smooth g _ _).contDiffAt.of_le
      (by exact_mod_cast le_top)), smul_comm]

lemma norm_wtd (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) (g : ES m n r s d) :
    ‖wtd p q g‖ = ‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2‖ := by
  simp only [wtd, LinearMap.coe_mk, AddHom.coe_mk]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

def snq (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) : Seminorm ℂ (ES m n r s d) :=
  (normSeminorm ℂ _).comp (wtd p q)

lemma snq_apply (p : ℕ × ℕ × ℕ) (q : QQ m n r s d) (g : ES m n r s d) :
    snq p q g = ‖wtd p q g‖ := rfl

lemma snq_bdd (p : ℕ × ℕ × ℕ) : BddAbove (range (snq (m := m) (n := n) (r := r) (d := d) p)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro g
  obtain ⟨C, hC⟩ := (rd g).2 p.1 p.2.1 p.2.2
  exact ⟨C, by rintro _ ⟨q, rfl⟩; show snq p q g ≤ C; rw [snq_apply, norm_wtd]; exact hC _ _ _⟩

/-- the seminorms of `S(ℝ^m × 𝕋^n × ℤ^r × F)` -/
def sn (p : ℕ × ℕ × ℕ) : Seminorm ℂ (ES m n r s d) := ⨆ q, snq p q

lemma sn_apply (p : ℕ × ℕ × ℕ) (g : ES m n r s d) : sn p g = ⨆ q, ‖wtd p q g‖ := by
  rw [sn, Seminorm.coe_iSup_eq (snq_bdd p), iSup_apply]; rfl

lemma le_sn (p : ℕ × ℕ × ℕ) (g : ES m n r s d) (q : QQ m n r s d) :
    ‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2‖ ≤ sn p g := by
  rw [← norm_wtd, sn_apply]
  obtain ⟨C, hC⟩ := (rd g).2 p.1 p.2.1 p.2.2
  refine le_ciSup (f := fun q => ‖wtd p q g‖) ⟨C, ?_⟩ q
  rintro _ ⟨q, rfl⟩; show ‖wtd p q g‖ ≤ C; rw [norm_wtd]; exact hC _ _ _

lemma sn_le (p : ℕ × ℕ × ℕ) (g : ES m n r s d) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ a b xt, ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift g.toFun a b) xt‖ ≤ M) : sn p g ≤ M := by
  rw [sn_apply]
  refine ciSup_le fun q => ?_
  rw [norm_wtd]; exact h _ _ _

/-- the map defining the topology -/
def Φ : ES m n r s d →+ ((p : ℕ × ℕ × ℕ) →
    UniformFun (QQ m n r s d) (ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ)) where
  toFun g p := UniformFun.ofFun (fun q => wtd p q g)
  map_zero' := by funext p; simp only [map_zero]; rfl
  map_add' f g := by funext p; simp only [map_add]; rfl

lemma top_eq : (inferInstance : TopologicalSpace (ES m n r s d)) =
    TopologicalSpace.induced (Φ (m := m) (n := n) (r := r) (d := d)) inferInstance := rfl

instance esTG : IsTopologicalAddGroup (ES m n r s d) :=
  topologicalAddGroup_induced (Φ (m := m) (n := n) (r := r) (d := d))

lemma comap_eq (p : ℕ × ℕ × ℕ) :
    (𝓝 (0 : UniformFun (QQ m n r s d) (ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ))).comap
      (fun g : ES m n r s d => Φ g p) = (𝓝 0).comap (sn (m := m) (n := n) (r := r) (d := d) p) := by
  have hb := (UniformFun.hasBasis_nhds_zero_of_basis (α := QQ m n r s d)
    (Metric.nhds_basis_ball (x := (0 : ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => XT m n) ℂ)))).comap
    (fun g : ES m n r s d => Φ g p)
  have hb2 := (Metric.nhds_basis_ball (x := (0 : ℝ))).comap (sn (m := m) (n := n) (r := r) (d := d) p)
  refine le_antisymm ?_ ?_
  · rw [hb.le_basis_iff hb2]
    intro ε hε
    refine ⟨ε / 2, half_pos hε, fun g hg => ?_⟩
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)]
    have : sn p g ≤ ε / 2 := by
      rw [sn_apply]
      refine ciSup_le fun q => ?_
      have := hg q
      simp only [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    linarith
  · rw [hb2.le_basis_iff hb]
    intro ε hε
    refine ⟨ε, hε, fun g hg q => ?_⟩
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg _ _)] at hg
    simp only [Metric.mem_ball, dist_zero_right]
    show ‖wtd p q g‖ < ε
    refine lt_of_le_of_lt ?_ hg
    rw [norm_wtd]; exact le_sn p g q

theorem es_ws : WithSeminorms (sn (m := m) (n := n) (r := r) (d := d)) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  have h0 : 𝓝 (0 : ES m n r s d) = comap (Φ (m := m) (n := n) (r := r) (d := d)) (𝓝 0) := by
    have h := @nhds_induced _ _ _ (Φ (m := m) (n := n) (r := r) (d := d)) 0
    rw [map_zero] at h
    exact h
  rw [h0, nhds_pi, Filter.pi, Filter.comap_iInf]
  refine iInf_congr fun p => ?_
  rw [Filter.comap_comap]
  exact comap_eq p

end

end MasulloGRHWFAux

namespace MasulloGRHWFAux

open MasulloGRH Topology Filter Set

noncomputable section

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma ws_all {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {ι : Type*} {p : SeminormFamily ℂ E ι} (hp : WithSeminorms p) :
    WithSeminorms (fun q : {q : Seminorm ℂ E // Continuous q} => q.1) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm (le_iInf fun q => ?_) ?_
  · rw [← tendsto_iff_comap]
    have := q.2.tendsto 0
    rwa [map_zero] at this
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf p).1 hp]
    exact le_iInf fun i => iInf_le_of_le ⟨p i, hp.continuous_seminorm i⟩ le_rfl

/-! ### derivatives of exponentials of linear forms -/

lemma iteratedDeriv_cexp (k : ℝ) (l : ℕ) :
    iteratedDeriv l (fun t : ℝ => k * Real.exp t) = fun t : ℝ => k * Real.exp t := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    simp

lemma exp_clm_deriv (M : XT m n →L[ℝ] ℝ) (k : ℝ) (l : ℕ) (v : XT m n) :
    ‖iteratedFDeriv ℝ l (fun v => k * Real.exp (M v)) v‖ ≤ |k| * Real.exp (M v) * ‖M‖ ^ l := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => k * Real.exp t) :=
    contDiff_const.mul Real.contDiff_exp
  have h1 : (fun v => k * Real.exp (M v)) = (fun t : ℝ => k * Real.exp t) ∘ M := rfl
  rw [h1, M.iteratedFDeriv_comp_right hs v (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp]
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  exact le_rfl

lemma leib (F : XT m n → ℂ) (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (M : XT m n →L[ℝ] ℝ)
    (k : ℝ) (K : ℕ) (v : XT m n) :
    ‖iteratedFDeriv ℝ K (fun v => ((k * Real.exp (M v) : ℝ) : ℂ) * F v) v‖ ≤
      |k| * Real.exp (M v) * ∑ l ∈ Finset.range (K + 1),
        (K.choose l : ℝ) * ‖M‖ ^ l * ‖iteratedFDeriv ℝ (K - l) F v‖ := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => k * Real.exp (M v)) :=
    contDiff_const.mul (Real.contDiff_exp.comp M.contDiff)
  have h := norm_iteratedFDeriv_smul_le hf hF v (n := K) (by exact_mod_cast le_top)
  have he : (fun v => ((k * Real.exp (M v) : ℝ) : ℂ) * F v) =
      fun v => (k * Real.exp (M v)) • F v := by
    funext v; rw [Complex.real_smul]
  rw [he]
  refine h.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have h2 := exp_clm_deriv M k l v
  calc (K.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun v => k * Real.exp (M v)) v‖ *
        ‖iteratedFDeriv ℝ (K - l) F v‖
      ≤ (K.choose l : ℝ) * (|k| * Real.exp (M v) * ‖M‖ ^ l) *
        ‖iteratedFDeriv ℝ (K - l) F v‖ := by gcongr
    _ = _ := by ring

/-! ### the shape of a continuous positive character -/

lemma mu_zero (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e)
    (hμmul : ∀ e e', μ (e + e') = μ e * μ e') : μ 0 = 1 := by
  have h := hμmul 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hμpos 0).ne' (by rw [mul_one]; exact h.symm)

def emb (m n r s : ℕ) (d : Fin s → ℕ) (v : XT m n) : ElemGroup m n r s d :=
  (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), 0, 0)

lemma emb_zero : emb m n r s d 0 = 0 := by
  unfold emb
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext j; rfl

lemma emb_add (v w : XT m n) : emb m n r s d (v + w) = emb m n r s d v + emb m n r s d w := by
  unfold emb
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext j; rfl
  · simp
  · simp

lemma emb_cont : Continuous (emb m n r s d) := by
  unfold emb
  refine continuous_fst.prodMk (Continuous.prodMk (continuous_pi fun j => ?_) continuous_const)
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp ((continuous_apply j).comp continuous_snd)

lemma mu_shape (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e)
    (hμmul : ∀ e e', μ (e + e') = μ e * μ e') (hμc : Continuous μ) :
    ∃ L : XT m n →L[ℝ] ℝ, ∀ (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) (v : XT m n),
      μ (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) =
        μ (0, 0, a, b) * Real.exp (L v) := by
  let f : XT m n →+ ℝ :=
    { toFun := fun v => Real.log (μ (emb m n r s d v))
      map_zero' := by rw [emb_zero, mu_zero μ hμpos hμmul, Real.log_one]
      map_add' := fun v w => by
        rw [emb_add, hμmul, Real.log_mul (hμpos _).ne' (hμpos _).ne'] }
  have hf : Continuous f :=
    (hμc.comp emb_cont).log fun v => (hμpos _).ne'
  refine ⟨f.toRealLinearMap hf, fun a b v => ?_⟩
  have h1 : (f.toRealLinearMap hf) v = Real.log (μ (emb m n r s d v)) := rfl
  rw [h1, Real.exp_log (hμpos _)]
  have h2 : ((v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) : ElemGroup m n r s d) =
      (0, 0, a, b) + emb m n r s d v := by
    unfold emb
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp
  rw [h2, hμmul]

/-! ### point evaluations -/

lemma norm_toFun_le (g : ES m n r s d) (e : ElemGroup m n r s d) :
    ‖g.toFun e‖ ≤ sn (0, 0, 0) g := by
  obtain ⟨x, z, a, b⟩ := e
  have hy : ∀ j, ∃ y : ℝ, (y : UnitAddCircle) = z j := fun j => QuotientAddGroup.mk_surjective (z j)
  choose y hy using hy
  have h := le_sn (0, 0, 0) g (a, b, (x, y))
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
  have h2 : elemLift g.toFun a b (x, y) = g.toFun (x, z, a, b) := by
    unfold elemLift
    simp only [hy]
  rwa [h2] at h

def evL (e : ElemGroup m n r s d) : ES m n r s d →ₗ[ℂ] ℂ where
  toFun g := g.toFun e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma ev_cont (e : ElemGroup m n r s d) : Continuous (fun g : ES m n r s d => g.toFun e) := by
  have hc : Continuous (sn (m := m) (n := n) (r := r) (d := d) (0, 0, 0)) :=
    es_ws.continuous_seminorm _
  have h0 := hc.tendsto 0
  rw [map_zero] at h0
  refine continuous_of_continuousAt_zero (evL e) ?_
  show Tendsto (evL e) (𝓝 0) (𝓝 (evL e 0))
  rw [map_zero]
  exact squeeze_zero_norm (fun g => norm_toFun_le g e) h0

/-! ### the interpolation estimate -/

def Bd (A B : ℝ) (K : ℕ) (sg sh : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (K + 1), (K.choose l : ℝ) * A ^ l *
    (sg (K - l) + ∑ l' ∈ Finset.range (K - l + 1),
      ((K - l).choose l' : ℝ) * B ^ l' * sh (K - l - l'))

lemma Bd_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (K : ℕ) {sg sh : ℕ → ℝ}
    (hsg : ∀ l, 0 ≤ sg l) (hsh : ∀ l, 0 ≤ sh l) : 0 ≤ Bd A B K sg sh := by
  unfold Bd
  refine Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (add_nonneg (hsg _) ?_)
  exact Finset.sum_nonneg fun l' _ => mul_nonneg (by positivity) (hsh _)

lemma rpow_interp {u θ β : ℝ} (hu : 0 < u) (h0 : 0 ≤ θ) (hθβ : θ ≤ β) : u ^ θ ≤ 1 + u ^ β := by
  rcases le_total u 1 with h | h
  · have := Real.rpow_le_one hu.le h h0
    have := Real.rpow_nonneg hu.le β
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hθβ
    linarith

lemma key_est (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e) (L : XT m n →L[ℝ] ℝ)
    (hL : ∀ (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) (v : XT m n),
      μ (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) = μ (0, 0, a, b) * Real.exp (L v))
    (θ β : ℝ) (h0 : 0 ≤ θ) (hθβ : θ ≤ β) (g g' h : ES m n r s d)
    (hg' : ∀ e, g'.toFun e = ((μ e ^ θ : ℝ) : ℂ) * g.toFun e)
    (hh : ∀ e, h.toFun e = ((μ e ^ β : ℝ) : ℂ) * g.toFun e) (i j K : ℕ) :
    sn (i, j, K) g' ≤ Bd ‖θ • L‖ ‖(-β) • L‖ K (fun l => sn (i, j, l) g) (fun l => sn (i, j, l) h) := by
  refine sn_le _ _ (Bd_nonneg (norm_nonneg _) (norm_nonneg _) K (fun _ => apply_nonneg _ _)
    (fun _ => apply_nonneg _ _)) fun a b v => ?_
  set c := μ (0, 0, a, b) with hcdef
  have hc : 0 < c := hμpos _
  have hcb : 0 < c ^ β := Real.rpow_pos_of_pos hc β
  have hG' : elemLift g'.toFun a b =
      fun w => ((c ^ θ * Real.exp ((θ • L) w) : ℝ) : ℂ) * elemLift g.toFun a b w := by
    funext w
    show g'.toFun (w.1, _, a, b) = _ * g.toFun (w.1, _, a, b)
    rw [hg', hL a b w, Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
    simp [mul_comm]
  have hG : elemLift g.toFun a b =
      fun w => ((c ^ (-β) * Real.exp (((-β) • L) w) : ℝ) : ℂ) * elemLift h.toFun a b w := by
    funext w
    show g.toFun (w.1, _, a, b) = _ * h.toFun (w.1, _, a, b)
    rw [hh, hL a b w, Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul, ← mul_assoc,
      ← Complex.ofReal_mul]
    have : c ^ (-β) * Real.exp (((-β) • L) w) * (c ^ β * Real.exp (L w * β)) = 1 := by
      rw [Real.rpow_neg hc.le, smul_apply, smul_eq_mul,
        show (-β) * L w = -(L w * β) by ring, Real.exp_neg]
      have := Real.exp_pos (L w * β)
      field_simp
    rw [this, Complex.ofReal_one, one_mul]
  set u := c * Real.exp (L v) with hudef
  have hu : 0 < u := mul_pos hc (Real.exp_pos _)
  have huθ : |c ^ θ| * Real.exp ((θ • L) v) = u ^ θ := by
    rw [hudef, Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul,
      abs_of_pos (Real.rpow_pos_of_pos hc θ), smul_apply, smul_eq_mul,
      mul_comm θ]
  have huβ : u ^ β * (|c ^ (-β)| * Real.exp (((-β) • L) v)) = 1 := by
    rw [hudef, Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul,
      abs_of_pos (Real.rpow_pos_of_pos hc _), Real.rpow_neg hc.le,
      smul_apply, smul_eq_mul,
      show (-β) * L v = -(L v * β) by ring, Real.exp_neg]
    have := Real.exp_pos (L v * β)
    field_simp
  have h1 := leib (elemLift g.toFun a b) (lift_smooth g a b) (θ • L) (c ^ θ) K v
  rw [← hG', huθ] at h1
  have h2 : ∀ J : ℕ, u ^ β * ‖iteratedFDeriv ℝ J (elemLift g.toFun a b) v‖ ≤
      ∑ l' ∈ Finset.range (J + 1), (J.choose l' : ℝ) * ‖(-β) • L‖ ^ l' *
        ‖iteratedFDeriv ℝ (J - l') (elemLift h.toFun a b) v‖ := by
    intro J
    have h3 := leib (elemLift h.toFun a b) (lift_smooth h a b) ((-β) • L) (c ^ (-β)) J v
    rw [← hG] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hu.le β)
    rwa [← mul_assoc, huβ, one_mul] at h4
  set wt := ‖a‖ ^ j * ‖v.1‖ ^ i with hwt
  have hw : 0 ≤ wt := by positivity
  set S := ∑ l ∈ Finset.range (K + 1),
        (K.choose l : ℝ) * ‖θ • L‖ ^ l * ‖iteratedFDeriv ℝ (K - l) (elemLift g.toFun a b) v‖ with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
  have h5 : u ^ θ * S ≤ (1 + u ^ β) * S :=
    mul_le_mul_of_nonneg_right (rpow_interp hu h0 hθβ) hSnn
  show wt * ‖iteratedFDeriv ℝ K (elemLift g'.toFun a b) v‖ ≤ _
  calc wt * ‖iteratedFDeriv ℝ K (elemLift g'.toFun a b) v‖
      ≤ wt * ((1 + u ^ β) * S) := mul_le_mul_of_nonneg_left (h1.trans h5) hw
    _ = ∑ l ∈ Finset.range (K + 1), (K.choose l : ℝ) * ‖θ • L‖ ^ l *
          (wt * ‖iteratedFDeriv ℝ (K - l) (elemLift g.toFun a b) v‖ +
            wt * (u ^ β * ‖iteratedFDeriv ℝ (K - l) (elemLift g.toFun a b) v‖)) := by
        rw [hS, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := by
        unfold Bd
        refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
          (by positivity)
        · exact le_sn (i, j, K - l) g (a, b, v)
        · refine (mul_le_mul_of_nonneg_left (h2 (K - l)) hw).trans ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun l' _ => ?_
          calc wt * ((↑((K - l).choose l') : ℝ) * ‖(-β) • L‖ ^ l' *
                ‖iteratedFDeriv ℝ (K - l - l') (elemLift h.toFun a b) v‖)
              = (↑((K - l).choose l') : ℝ) * ‖(-β) • L‖ ^ l' *
                (wt * ‖iteratedFDeriv ℝ (K - l - l') (elemLift h.toFun a b) v‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_sn (i, j, K - l - l') h (a, b, v))
                (by positivity)

lemma cont_between {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X]
    (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e) (L : XT m n →L[ℝ] ℝ)
    (hL : ∀ (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)) (v : XT m n),
      μ (v.1, fun j => ((v.2 j : ℝ) : UnitAddCircle), a, b) = μ (0, 0, a, b) * Real.exp (L v))
    (Wa Wb Wc : X →ₗ[ℂ] ES m n r s d) (hca : Continuous Wa) (hcb : Continuous Wb)
    (θ β : ℝ) (h0 : 0 ≤ θ) (hθβ : θ ≤ β)
    (h1 : ∀ x e, (Wc x).toFun e = ((μ e ^ θ : ℝ) : ℂ) * (Wa x).toFun e)
    (h2 : ∀ x e, (Wb x).toFun e = ((μ e ^ β : ℝ) : ℂ) * (Wa x).toFun e) : Continuous Wc := by
  refine WithSeminorms.continuous_of_continuous_comp es_ws Wc fun p => ?_
  obtain ⟨i, j, K⟩ := p
  refine Seminorm.continuous_of_continuousAt_zero ?_
  have hsc : ∀ (p : ℕ × ℕ × ℕ) (V : X →ₗ[ℂ] ES m n r s d), Continuous V →
      Continuous fun x => sn p (V x) := fun p V hV => (es_ws.continuous_seminorm p).comp hV
  have hF : Continuous fun x : X => Bd ‖θ • L‖ ‖(-β) • L‖ K (fun l => sn (i, j, l) (Wa x))
      (fun l => sn (i, j, l) (Wb x)) := by
    unfold Bd
    exact continuous_finsetSum _ fun l _ => continuous_const.mul ((hsc _ Wa hca).add
      (continuous_finsetSum _ fun l' _ => continuous_const.mul (hsc _ Wb hcb)))
  have hF0 := hF.tendsto 0
  have hz : Bd ‖θ • L‖ ‖(-β) • L‖ K (fun l => sn (i, j, l) (Wa (0 : X)))
      (fun l => sn (i, j, l) (Wb (0 : X))) = 0 := by
    simp [Bd]
  rw [hz] at hF0
  show Tendsto (fun x => ((sn (i, j, K)).comp Wc) x) (𝓝 0) (𝓝 (((sn (i, j, K)).comp Wc) 0))
  rw [map_zero]
  exact squeeze_zero (fun x => apply_nonneg _ _)
    (fun x => key_est μ hμpos L hL θ β h0 hθβ (Wa x) (Wc x) (Wb x) (h1 x) (h2 x) i j K) hF0

/-! ### the countable set of exponents -/

def DD (I : Set ℝ) : Set ℝ :=
  {c | c ∈ I ∧ (c ∈ Set.range ((↑) : ℚ → ℝ) ∨ IsGreatest I c ∨ IsLeast I c)}

lemma DD_sub {I : Set ℝ} {c : ℝ} (h : c ∈ DD I) : c ∈ I := h.1

lemma DD_countable (I : Set ℝ) : (DD I).Countable := by
  refine Set.Countable.mono (s₂ := Set.range ((↑) : ℚ → ℝ) ∪ ({c | IsGreatest I c} ∪ {c | IsLeast I c}))
    (fun c hc => hc.2) ?_
  refine (Set.countable_range _).union (Set.Countable.union ?_ ?_)
  · exact Set.Subsingleton.countable fun x hx y hy => hx.unique hy
  · exact Set.Subsingleton.countable fun x hx y hy => hx.unique hy

lemma DD_above {I : Set ℝ} (hI : I.OrdConnected) {c : ℝ} (hc : c ∈ I) : ∃ b ∈ DD I, c ≤ b := by
  by_cases h : ∃ c' ∈ I, c < c'
  · obtain ⟨c', hc', hlt⟩ := h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact ⟨q, ⟨hI.out hc hc' ⟨hq1.le, hq2.le⟩, Or.inl ⟨q, rfl⟩⟩, hq1.le⟩
  · push Not at h
    exact ⟨c, ⟨hc, Or.inr (Or.inl ⟨hc, fun x hx => h x hx⟩)⟩, le_rfl⟩

lemma DD_below {I : Set ℝ} (hI : I.OrdConnected) {c : ℝ} (hc : c ∈ I) : ∃ a ∈ DD I, a ≤ c := by
  by_cases h : ∃ c' ∈ I, c' < c
  · obtain ⟨c', hc', hlt⟩ := h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    exact ⟨q, ⟨hI.out hc' hc ⟨hq1.le, hq2.le⟩, Or.inl ⟨q, rfl⟩⟩, hq2.le⟩
  · push Not at h
    exact ⟨c, ⟨hc, Or.inr (Or.inr ⟨hc, fun x hx => h x hx⟩)⟩, le_rfl⟩

lemma topD_le {X : Type*} [AddCommGroup X] [Module ℂ X]
    (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e)
    (hμmul : ∀ e e', μ (e + e') = μ e * μ e') (hμc : Continuous μ)
    (I : Set ℝ) (hI : I.OrdConnected)
    (W : ℝ → X →ₗ[ℂ] ES m n r s d)
    (hW : ∀ a ∈ I, ∀ b ∈ I, ∀ (x : X) (e : ElemGroup m n r s d),
      (W a x).toFun e = ((μ e ^ (a - b) : ℝ) : ℂ) * (W b x).toFun e)
    (c : ℝ) (hc : c ∈ I) :
    (⨅ a : DD I, TopologicalSpace.induced (W a) inferInstance) ≤
      TopologicalSpace.induced (W c) inferInstance := by
  obtain ⟨L, hL⟩ := mu_shape μ hμpos hμmul hμc
  obtain ⟨a, ha, hac⟩ := DD_below hI hc
  obtain ⟨b, hb, hcb⟩ := DD_above hI hc
  letI τ : TopologicalSpace X := ⨅ a : DD I, TopologicalSpace.induced (W a) inferInstance
  haveI : IsTopologicalAddGroup X :=
    (withSeminorms_iInf (fun a : DD I => LinearMap.withSeminorms_induced
      (es_ws (m := m) (n := n) (r := r) (d := d)) (W a))).topologicalAddGroup
  have hca : Continuous (W a) :=
    continuous_iff_le_induced.2 (iInf_le _ (⟨a, ha⟩ : DD I))
  have hcb' : Continuous (W b) :=
    continuous_iff_le_induced.2 (iInf_le _ (⟨b, hb⟩ : DD I))
  rw [← continuous_iff_le_induced]
  exact cont_between μ hμpos L hL (W a) (W b) (W c) hca hcb' (c - a) (b - a) (by linarith)
    (by linarith) (fun x e => hW c hc a (DD_sub ha) x e) (fun x e => hW b (DD_sub hb) a (DD_sub ha) x e)

end

end MasulloGRHWFAux

open MasulloGRH MasulloGRHWFAux Topology Filter in
theorem solution
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (μ : ElemGroup m n r s d → ℝ) (hμpos : ∀ e, 0 < μ e)
    (hμmul : ∀ e e', μ (e + e') = μ e * μ e') (hμc : Continuous μ)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty)
    (X : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (W : ℝ → X →ₗ[ℂ] ElemSchwartz m n r s d)
    (hW : ∀ a ∈ I, ∀ b ∈ I, ∀ (x : X) (e : ElemGroup m n r s d),
      (W a x).toFun e = ((μ e ^ (a - b) : ℝ) : ℂ) * (W b x).toFun e)
    (htop : ‹TopologicalSpace X› =
      ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (W a) inferInstance)
    (hinj : ∀ x : X, (∀ a ∈ I, W a x = 0) → x = 0)
    (hsurj : ∀ g : ℝ → ElemSchwartz m n r s d,
      (∀ a ∈ I, ∀ b ∈ I, ∀ e : ElemGroup m n r s d,
        (g a).toFun e = ((μ e ^ (a - b) : ℝ) : ℂ) * (g b).toFun e) →
      ∃ x : X, ∀ a ∈ I, W a x = g a) :
    IsFrechet X := by
  obtain ⟨hFr, -⟩ := elemSchwartz_frechet_nuclear_montel m n r s d hd
  obtain ⟨-, ⟨hT2, hcomp⟩, -⟩ := hFr
  haveI := hT2
  have htopD : ‹TopologicalSpace X› =
      ⨅ a : DD I, TopologicalSpace.induced (W a) inferInstance := by
    rw [htop]
    refine le_antisymm (le_iInf fun a => iInf₂_le a.1 (DD_sub a.2)) ?_
    exact le_iInf₂ fun c hc => topD_le μ hμpos hμmul hμc I hI W hW c hc
  have hws : WithSeminorms (SeminormFamily.sigma fun a : DD I =>
      SeminormFamily.comp (sn (m := m) (n := n) (r := r) (d := d)) (W a)) := by
    rw [htopD]
    exact withSeminorms_iInf fun a : DD I => LinearMap.withSeminorms_induced es_ws (W a)
  haveI : IsTopologicalAddGroup X := hws.topologicalAddGroup
  haveI : Countable (DD I) := (DD_countable I).to_subtype
  haveI : FirstCountableTopology X := hws.firstCountableTopology
  have hWc : ∀ a ∈ I, Continuous (W a) := fun a ha => by
    rw [continuous_iff_le_induced, htop]
    exact iInf₂_le a ha
  haveI hT2X : T2Space X := by
    refine T2Space.of_injective_continuous (f := fun (x : X) (a : I) => W a x) ?_
      (continuous_pi fun a => hWc a a.2)
    intro x y h
    refine sub_eq_zero.1 (hinj _ fun a ha => ?_)
    rw [map_sub, sub_eq_zero]
    exact congrFun h ⟨a, ha⟩
  have hmetX : TopologicalSpace.MetrizableSpace X := by
    letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
    haveI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
    haveI : (uniformity X).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
    exact UniformSpace.metrizableSpace
  refine ⟨⟨{q : Seminorm ℂ X // Continuous q}, ⟨⟨0, continuous_const⟩⟩, _, ws_all hws⟩,
    ⟨hT2X, fun f hf => ?_⟩, hmetX⟩
  obtain ⟨hne', hcf⟩ := hf
  haveI := hne'
  have hex : ∀ a ∈ I, ∃ z, map (W a) f ≤ 𝓝 z := fun a ha =>
    hcomp (map (W a) f) ⟨Filter.map_neBot, fun U hU => by
      obtain ⟨A, hA, hAU⟩ := hcf _ ((hWc a ha).tendsto 0 (by rw [map_zero]; exact hU))
      refine ⟨W a '' A, image_mem_map hA, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_sub]; exact hAU x hx y hy⟩
  classical
  let g : ℝ → ElemSchwartz m n r s d := fun a => if ha : a ∈ I then (hex a ha).choose else 0
  have hg : ∀ a ∈ I, map (W a) f ≤ 𝓝 (g a) := fun a ha => by
    simp only [g, dif_pos ha]; exact (hex a ha).choose_spec
  obtain ⟨x, hx⟩ := hsurj g (fun a ha b hb e => by
    have h1 : Tendsto (fun y => (W a y).toFun e) f (𝓝 ((g a).toFun e)) :=
      ((ev_cont e).tendsto (g a)).comp (hg a ha)
    have h2 : Tendsto (fun y => ((μ e ^ (a - b) : ℝ) : ℂ) * (W b y).toFun e) f
        (𝓝 (((μ e ^ (a - b) : ℝ) : ℂ) * (g b).toFun e)) :=
      (((ev_cont e).tendsto (g b)).comp (hg b hb)).const_mul _
    have h3 : (fun y => (W a y).toFun e) =
        fun y => ((μ e ^ (a - b) : ℝ) : ℂ) * (W b y).toFun e := funext fun y => hW a ha b hb y e
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2)
  refine ⟨x, ?_⟩
  rw [htop, nhds_iInf]
  refine le_iInf fun a => ?_
  rw [nhds_iInf]
  refine le_iInf fun ha => ?_
  rw [nhds_induced, ← map_le_iff_le_comap, hx a ha]
  exact hg a ha
