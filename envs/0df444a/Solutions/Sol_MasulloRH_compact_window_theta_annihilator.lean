-- Prove2me | solution 1 for MasulloRH.compact_window_theta_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:57:46.652861+00:00
-- url     : https://prove2.me/submissions/ba9112a6-4c29-4ac1-bbb3-467b3a8c49cf

import Mathlib
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv

open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

private lemma smooth_division_once (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a : ℝ) (ha : f a = 0) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ∀ x, f x = ((x-a:ℝ):ℂ) * g x := by
  let F (p : ℝ × ℝ) := f (p.1 + p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp (contDiff_fst.add contDiff_snd)
  let G (p : ℝ × ℝ) := ∫ θ in (0:ℝ)..1, fderiv ℝ (fun t => F (p.1,t)) (θ • p.2)
  obtain ⟨hG,hfac⟩ := FiniteEnergyPlane.hadamard_integral_fderiv F hF
  let g (x : ℝ) := G (a,x-a) 1
  have hpair : ContDiff ℝ ∞ (fun x : ℝ => (a, x-a)) := contDiff_const.prodMk (contDiff_id.sub contDiff_const)
  refine ⟨g,(hG.comp hpair).clm_apply contDiff_const,fun x => ?_⟩
  have heq : f x = G (a,x-a) (x-a) := by simpa [F, G, ha] using hfac (a,x-a)
  have hlin := (G (a,x-a)).map_smul (x-a) (1:ℝ)
  rw [smul_eq_mul, mul_one, Complex.real_smul] at hlin
  exact heq.trans hlin

private lemma factor_jet (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (a : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n+1) (fun u : ℝ => ((u-a:ℝ):ℂ) * g u) x =
      ((x-a:ℝ):ℂ) * iteratedDeriv (n+1) g x + (n+1 : ℕ) * iteratedDeriv n g x := by
  have hd (k : ℕ) (y : ℝ) : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k+1) g y) y := by
    rw [iteratedDeriv_succ]
    exact (hg.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k) y).hasDerivAt
  have hl (y : ℝ) : HasDerivAt (fun u : ℝ => ((u-a:ℝ):ℂ)) 1 y := by
    simpa using ((hasDerivAt_id y).sub_const a).ofReal_comp
  induction n generalizing x with
  | zero =>
    have h := (hl x).mul ((hg.differentiable (by simp) x).hasDerivAt)
    simpa [Pi.mul_def, iteratedDeriv_succ, mul_comm ((x-a:ℝ):ℂ), add_comm] using h.deriv
  | succ n ih =>
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv (n+1) (fun u : ℝ => ((u-a:ℝ):ℂ) * g u) =
      (fun y : ℝ => ((y-a:ℝ):ℂ) * iteratedDeriv (n+1) g y + (n+1:ℕ) * iteratedDeriv n g y) from funext ih]
    have he := (((hl x).mul (hd (n+1) x)).add ((hd n x).const_mul ((n+1:ℕ):ℂ))).deriv
    simp only [Pi.mul_def, Pi.add_def] at he
    rw [he]
    push_cast
    ring

private lemma smooth_division_pow (a : ℝ) (n : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hz : ∀ k < n, iteratedDeriv k f a = 0) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ∀ x, f x = ((x-a:ℝ):ℂ)^n * g x := by
  induction n generalizing f with
  | zero => exact ⟨f,hf,fun _ => by simp⟩
  | succ n ih =>
    obtain ⟨q,hq,hfac⟩ := smooth_division_once f hf a (by simpa using hz 0 (Nat.succ_pos n))
    have hqz (k : ℕ) (hk : k < n) : iteratedDeriv k q a = 0 := by
      have h := hz (k+1) (Nat.succ_lt_succ hk)
      rw [funext hfac, factor_jet q hq] at h
      have hk0 : ((k+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      simp only [sub_self, Complex.ofReal_zero, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hk0
    obtain ⟨g,hg,he⟩ := ih q hq hqz
    exact ⟨g,hg,fun x => by rw [hfac,he,pow_succ]; ring⟩

private lemma compact_smooth_division {G f : ℝ → ℂ} (hG : ∀ a, AnalyticAt ℝ G a)
    (hfinite : ∀ a, analyticOrderAt G a ≠ ⊤)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hzero : ∀ a k, k < analyticOrderNatAt G a → iteratedDeriv k f a = 0) :
    ∃ q : ℝ → ℂ, ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧ ∀ x, f x = G x * q x := by
  classical
  have hlocal (a : ℝ) : ∃ q : ℝ → ℂ, ContDiffAt ℝ ∞ q a ∧
      (∀ᶠ x in 𝓝 a, f x = G x * q x) ∧ (a ∉ tsupport f → q a = 0) := by
    by_cases ha : a ∈ tsupport f
    · obtain ⟨g,hga,hgne,hg⟩ := ((hG a).analyticOrderNatAt_eq_iff (hfinite a)).mp rfl
      obtain ⟨v,hv,hvf⟩ := smooth_division_pow a (analyticOrderNatAt G a) f hf (hzero a)
      refine ⟨fun x => v x / g x, (by simpa only [div_eq_mul_inv, Pi.inv_apply] using hv.contDiffAt.mul (hga.contDiffAt.inv hgne)), ?_, fun h => (h ha).elim⟩
      filter_upwards [hg,hga.continuousAt.eventually_ne hgne] with x hx hne
      rw [hvf, hx, Complex.real_smul, Complex.ofReal_pow]
      field_simp
    · refine ⟨0,contDiffAt_const, ?_, fun _ => rfl⟩
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ha] with x hx
      simpa only [Pi.zero_apply, mul_zero] using hx
  choose q hq he hs using hlocal
  let Q (x : ℝ) := q x x
  have hQ (x : ℝ) : f x = G x * Q x := (he x).self_of_nhds
  have hQs : ContDiff ℝ ∞ Q := by
    apply contDiff_iff_contDiffAt.mpr
    intro a
    apply (hq a).congr_of_eventuallyEq
    obtain ⟨g,hga,hgne,hg⟩ := ((hG a).analyticOrderNatAt_eq_iff (hfinite a)).mp rfl
    filter_upwards [hg,hga.continuousAt.eventually_ne hgne, he a] with x hx hgx heq
    by_cases hxa : x = a
    · subst x; rfl
    · have hGx : G x ≠ 0 := by
        rw [hx]
        exact smul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hxa)) hgx
      exact mul_left_cancel₀ hGx ((hQ x).symm.trans heq)
  have hsub : Function.support Q ⊆ tsupport f := by
    intro x hx
    by_contra ha
    exact hx (hs x ha)
  exact ⟨Q,hQs,hc.of_isClosed_subset (isClosed_tsupport Q) (closure_minimal hsub (isClosed_tsupport f)), hQ⟩




open scoped SchwartzMap Topology ContDiff
open Set Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

private lemma finite_compact_analytic_roots {G : ℝ → ℂ} (hG : ∀ x, AnalyticAt ℝ G x)
    (hfin : ∀ x, analyticOrderAt G x ≠ ⊤) {K : Set ℝ} (hK : IsCompact K) :
    {x ∈ K | G x = 0}.Finite := by
  by_contra h
  obtain ⟨x,_,hx⟩ := (Set.not_finite.mp h).exists_accPt_of_subset_isCompact hK (fun _ hi => hi.1)
  have hfreq : ∃ᶠ y in 𝓝[≠] x, G y = 0 := by
    rw [frequently_nhdsWithin_iff]
    exact (accPt_iff_frequently.mp hx).mono fun y hy => ⟨hy.2.2,hy.1⟩
  exact hfin x (analyticOrderAt_eq_top.mpr ((hG x).frequently_zero_iff_eventually_zero.mp hfreq))

private noncomputable def jetLine (a : ℝ) (r : ℕ) : 𝓢(ℝ,ℂ) →ₗ[ℂ] ℂ where
  toFun f := iteratedDeriv r f a
  map_add' f g := iteratedDeriv_add (f.contDiffAt r) (g.contDiffAt r)
  map_smul' z f := by exact iteratedDeriv_const_smul_field (x:=a) (n:=r) z (f:ℝ→ℂ)

theorem solution {G : ℝ → ℂ} (hG : ∀ x, AnalyticAt ℝ G x)
    (hfin : ∀ x, analyticOrderAt G x ≠ ⊤)
    (u : 𝓢(ℝ,ℂ) →L[ℂ] ℂ)
    (hann : ∀ q t : 𝓢(ℝ,ℂ), HasCompactSupport (q:ℝ→ℂ) →
      (∀ x, t x = G x * q x) → u t = 0)
    (b : 𝓢(ℝ,ℂ)) (hb : HasCompactSupport (b:ℝ→ℂ)) :
    ∃ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ tsupport (b:ℝ→ℂ) ∧ G x = 0) ∧
      ∃ c : (a : S) → Fin (analyticOrderNatAt G a.val) → ℂ,
        ∀ f : 𝓢(ℝ,ℂ), u (SchwartzMap.smulLeftCLM ℂ (b:ℝ→ℂ) f) =
          ∑ a : S, ∑ k : Fin (analyticOrderNatAt G a.val), c a k * iteratedDeriv k.val f a.val := by
  classical
  let rootSet := {x ∈ tsupport (b:ℝ→ℂ) | G x = 0}
  have hroot : rootSet.Finite := finite_compact_analytic_roots hG hfin hb
  let S := hroot.toFinset
  have hS x : x ∈ S ↔ x ∈ tsupport (b:ℝ→ℂ) ∧ G x = 0 := hroot.mem_toFinset
  let J := (a : S) × Fin (analyticOrderNatAt G a.val)
  let L (j : J) := jetLine j.1.val j.2.val
  let M := (u.comp (SchwartzMap.smulLeftCLM ℂ (b:ℝ→ℂ))).toLinearMap
  have hker : ⨅ j, LinearMap.ker (L j) ≤ LinearMap.ker M := by
    intro f hf
    have hjet (a : S) (k : Fin (analyticOrderNatAt G a.val)) : iteratedDeriv k.val f a.val = 0 :=
      ((Submodule.mem_iInf _).mp hf ⟨a,k⟩ : f ∈ LinearMap.ker (L ⟨a,k⟩))
    let t := SchwartzMap.smulLeftCLM ℂ (b:ℝ→ℂ) f
    have ht (x : ℝ) : t x = b x * f x :=
      SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth f x
    have htc : HasCompactSupport (t:ℝ→ℂ) := by
      rw [funext ht]
      exact hb.mul_right
    have htjet (x : ℝ) (k : ℕ) (hk : k < analyticOrderNatAt G x) :
        iteratedDeriv k t x = 0 := by
      by_cases hxb : x ∈ tsupport (b:ℝ→ℂ)
      · have hGx : G x = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_zero_of_lt hk)
        let a : S := ⟨x,(hS x).mpr ⟨hxb,hGx⟩⟩
        rw [funext ht, iteratedDeriv_fun_mul (b.contDiffAt k) (f.contDiffAt k)]
        refine Finset.sum_eq_zero fun i _ => ?_
        have h' : k-i < analyticOrderNatAt G x := (Nat.sub_le _ _).trans_lt hk
        have hh := hjet a ⟨k-i,h'⟩
        simp only [a, hh, mul_zero]
      · have he : (t:ℝ→ℂ) =ᶠ[𝓝 x] (fun _ => (0:ℂ)) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxb] with y hy
          simp only [ht,hy,Pi.zero_apply,zero_mul]
        simpa only [iteratedDeriv_fun_const_zero] using he.iteratedDeriv_eq k
    obtain ⟨q,hq,hcq,he⟩ := compact_smooth_division hG hfin (t.smooth ⊤) htc htjet
    exact hann (hcq.toSchwartzMap hq) t hcq he
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨S,hS,fun a k => c ⟨a,k⟩,fun f => ?_⟩
  have he := LinearMap.congr_fun hc.symm f
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, J, Fintype.sum_sigma, M,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, L, jetLine, LinearMap.coe_mk,
    AddHom.coe_mk] using he
