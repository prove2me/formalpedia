-- Prove2me | solution 1 for LeiBR.Rand.eq5_gamma_contraction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:20:06.989208+00:00
-- url     : https://prove2.me/submissions/926f250a-2436-4654-a39c-b298588cb87d

import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
open MeasureTheory ProbabilityTheory

namespace LeiBR2AuxE5
open LeiBR.Rand

variable {N : ℕ} {n : Fin N → ℕ}

lemma cdAt {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hU.mem_nhds hx)

lemma hasD1 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((cdAt hU hf hx).differentiableAt (by norm_num)).hasFDerivAt

lemma hasD2 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
  (((cdAt hU hf hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

lemma symmD2 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) (v w : LeiBR.Sync.Profile n) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
  (cdAt hU hf hx).isSymmSndFDerivAt (by simp) v w

lemma hess_eq (g : LeiBR.Sync.Profile n → ℝ) (x : LeiBR.Sync.Profile n) (i j : Fin N)
    (u : LeiBR.Sync.Strat n i) (v : LeiBR.Sync.Strat n j) :
    hessBlock g x i j u v = fderiv ℝ (fderiv ℝ g) x (Pi.single i u) (Pi.single j v) := by
  simp [hessBlock, blockEmb]

lemma path_deriv (x : LeiBR.Sync.Profile n) (i : Fin N) (a v : LeiBR.Sync.Strat n i) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Function.update x i (a + s • v)) (Pi.single i v) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add a
  have h2 := (hasFDerivAt_update (𝕜 := ℝ) x (a + s • v)).comp_hasDerivAt s h1
  have e : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (LeiBR.Sync.Strat n i)))) v
      = Pi.single i v := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e] at h2
  exact h2


lemma pi_single_apply (i : Fin N) (v : LeiBR.Sync.Strat n i) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (LeiBR.Sync.Strat n i)))) v
      = (Pi.single i v : LeiBR.Sync.Profile n) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma foc {d : ℕ} (G : Game N n) {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M) {mu : ℝ}
    {xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n} (hxhat : IsProxBR G mu xhat)
    {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U) (hSU : {x | G.Feasible x} ⊆ U) (i : Fin N)
    (hf : ContDiffOn ℝ 2 (G.f i) U)
    (y : LeiBR.Sync.Profile n) (hy : G.Feasible y) (z : LeiBR.Sync.Strat n i) (hz : z ∈ G.X i) :
    0 ≤ fderiv ℝ (G.f i) (Function.update y i (xhat y i)) (Pi.single i (z - xhat y i)) +
      mu * inner ℝ (xhat y i - y i) (z - xhat y i) := by
  have hu := (hxhat y hy i).1
  have hP : Function.update y i (xhat y i) ∈ U := by
    apply hSU
    intro j
    by_cases h : j = i
    · subst h; simpa using hu
    · rw [Function.update_of_ne h]; exact hy j
  have h1 := (hasD1 hU hf hP).comp (xhat y i) (hasFDerivAt_update (𝕜 := ℝ) y (xhat y i))
  have h2 := (((hasFDerivAt_id (𝕜 := ℝ) (xhat y i)).sub_const (y i)).norm_sq).const_mul (mu / 2)
  have h := h1.add h2
  have hmin := (hxhat y hy i).2.localize
  have hseg : segment ℝ (xhat y i) (xhat y i + (z - xhat y i)) ⊆ G.X i := by
    rw [add_sub_cancel]; exact (hA1.convex i).segment_subset hu hz
  have := hmin.hasFDerivWithinAt_nonneg h.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, pi_single_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at this
  convert this using 2
  simp only [id]
  ring


lemma mvt {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {S : Set (LeiBR.Sync.Profile n)} (hS : Convex ℝ S) (hSU : S ⊆ U)
    {P P' : LeiBR.Sync.Profile n} (hP : P ∈ S) (hP' : P' ∈ S) (V : LeiBR.Sync.Profile n) :
    ∃ Q ∈ S, fderiv ℝ f P' V - fderiv ℝ f P V = fderiv ℝ (fderiv ℝ f) Q (P' - P) V := by
  set γ : ℝ → LeiBR.Sync.Profile n := fun s => P + s • (P' - P) with hγ
  have hγS : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ S := fun s hs => hS.add_smul_sub_mem hP hP' hs
  have hγd : ∀ s, HasDerivAt γ (P' - P) s := fun s => by
    have := ((hasDerivAt_id s).smul_const (P' - P)).const_add P
    simp only [id, one_smul] at this
    exact this
  have hcont : ContinuousOn (fun s => fderiv ℝ f (γ s) V) (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun s => fderiv ℝ f (γ s)) (Set.Icc 0 1) :=
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
        (Continuous.continuousOn (by fun_prop)) (fun s hs => hSU (hγS s hs))
    exact h1.clm_apply continuousOn_const
  have hder : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun s => fderiv ℝ f (γ s) V)
      (fderiv ℝ (fderiv ℝ f) (γ s) (P' - P) V) s := by
    intro s hs
    have hc := (hasD2 hU hf (hSU (hγS s (Set.Ioo_subset_Icc_self hs)))).comp_hasDerivAt s (hγd s)
    have := hc.clm_apply (hasDerivAt_const s V)
    simpa using this
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one hcont hder
  refine ⟨γ c, hγS c (Set.Ioo_subset_Icc_self hc), ?_⟩
  rw [hceq]
  simp [hγ]


lemma psd {d : ℕ} (G : Game N n) {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M)
    {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U) (hSU : {x | G.Feasible x} ⊆ U) (i : Fin N)
    (hf : ContDiffOn ℝ 2 (G.f i) U) (x : LeiBR.Sync.Profile n) (hx : G.Feasible x)
    (v : LeiBR.Sync.Strat n i) :
    0 ≤ fderiv ℝ (fderiv ℝ (G.f i)) x (Pi.single i v) (Pi.single i v) := by
  obtain ⟨V, hVo, hXV, hcv⟩ := hA1.convexOn i x hx
  set γ : ℝ → LeiBR.Sync.Strat n i := fun s => x i + s • v with hγ
  set pth : ℝ → LeiBR.Sync.Profile n := fun s => Function.update x i (γ s) with hpth
  have hγc : Continuous γ := by fun_prop
  have hpc : Continuous pth := Continuous.update continuous_const i hγc
  have hp0 : pth 0 = x := by simp [hpth, hγ]
  set W : Set ℝ := γ ⁻¹' V ∩ pth ⁻¹' U with hW
  have hWo : IsOpen W := (hVo.preimage hγc).inter (hU.preimage hpc)
  have h0W : (0:ℝ) ∈ W := ⟨by simpa [hγ] using hXV (hx i), by rw [Set.mem_preimage, hp0]; exact hSU hx⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hWo 0 h0W
  set I : Set ℝ := Set.Ioo (-δ) δ with hI
  have hIW : I ⊆ W := by
    intro s hs; apply hball; rw [Real.ball_eq_Ioo]; simpa [hI] using hs
  set k : ℝ → ℝ := fun s => G.f i (pth s) with hk
  have hkconv : ConvexOn ℝ I k := by
    refine ⟨convex_Ioo _ _, fun s hs t ht a b ha hb hab => ?_⟩
    have hγlin : γ (a • s + b • t) = a • γ s + b • γ t := by
      simp only [hγ, smul_eq_mul]
      rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hab, one_smul,
        add_smul]
    have := hcv.2 (hIW hs).1 (hIW ht).1 ha hb hab
    simp only [hk, hpth, smul_eq_mul] at this ⊢
    rw [show a * s + b * t = a • s + b • t by simp, hγlin]
    exact this
  have hkd : ∀ s ∈ I, HasDerivAt k (fderiv ℝ (G.f i) (pth s) (Pi.single i v)) s := by
    intro s hs
    have := (hasD1 hU hf (hIW hs).2).comp_hasDerivAt s (path_deriv x i (x i) v s)
    exact this
  have hmono : MonotoneOn (deriv k) I :=
    hkconv.monotoneOn_deriv fun s hs => (hkd s hs).differentiableAt
  set m : ℝ → ℝ := fun s => fderiv ℝ (G.f i) (pth s) (Pi.single i v) with hm
  have hmono' : MonotoneOn m I := by
    intro a ha b hb hab
    have h1 := hmono ha hb hab
    rwa [(hkd a ha).deriv, (hkd b hb).deriv] at h1
  have hmd : HasDerivAt m (fderiv ℝ (fderiv ℝ (G.f i)) x (Pi.single i v) (Pi.single i v)) 0 := by
    have hxU : pth 0 ∈ U := (hIW (by simp [hI, hδ])).2
    have hc := (hasD2 hU hf hxU).comp_hasDerivAt 0 (path_deriv x i (x i) v 0)
    have := hc.clm_apply (hasDerivAt_const (0:ℝ) (Pi.single i v : LeiBR.Sync.Profile n))
    simp only [map_zero, add_zero] at this
    rw [hp0] at this
    exact this
  have hacc : AccPt (0:ℝ) (Filter.principal I) := by
    rw [accPt_principal_iff_nhdsWithin]
    have h1 := left_nhdsWithin_Ioo_neBot (a := (0:ℝ)) hδ
    refine h1.mono (nhdsWithin_mono _ ?_)
    intro s hs
    simp only [Set.mem_Ioo] at hs
    refine ⟨⟨by linarith [hs.1], hs.2⟩, ?_⟩
    simp only [Set.mem_singleton_iff]; exact ne_of_gt hs.1
  exact hmd.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono'


lemma hess_contOn {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (i j : Fin N) : ContinuousOn (fun x => hessBlock f x i j) U := by
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U := h1.continuousOn_fderiv_of_isOpen hU le_rfl
  unfold hessBlock
  exact continuousOn_const.clm_comp (h2.clm_comp continuousOn_const)

lemma hess_bound {f : LeiBR.Sync.Profile n → ℝ} (x : LeiBR.Sync.Profile n) (i j : Fin N) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B) : ‖hessBlock f x i j‖ ≤ B := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ hB0 fun u v => ?_
  rw [hess_eq]
  calc ‖fderiv ℝ (fderiv ℝ f) x (Pi.single i u) (Pi.single j v)‖
      ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖(Pi.single i u : LeiBR.Sync.Profile n)‖ *
          ‖(Pi.single j v : LeiBR.Sync.Profile n)‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ B * ‖u‖ * ‖v‖ := by
        rw [Pi.norm_single, Pi.norm_single]
        gcongr

end LeiBR2AuxE5

open LeiBR.Rand LeiBR2AuxE5

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (y y' : LeiBR.Sync.Profile n) (hy : G.Feasible y) (hy' : G.Feasible y') (i : Fin N) :
    ‖xhat y' i - xhat y i‖ ≤ ∑ j, Gamma G mu i j * ‖y' j - y j‖ := by
  obtain ⟨U, hUo, hSU, hsm⟩ := hA1.smooth
  have hf := hsm i
  set S : Set (LeiBR.Sync.Profile n) := {x | G.Feasible x} with hSdef
  have hS : S = Set.univ.pi G.X := by ext x; simp [hSdef, Game.Feasible]
  have hSc : IsCompact S := hS ▸ isCompact_univ_pi hA1.compact
  have hScv : Convex ℝ S := by rw [hS]; exact convex_pi fun i _ => hA1.convex i
  have hu := (hxhat y hy i).1
  have hu' := (hxhat y' hy' i).1
  set u := xhat y i with hudef
  set u' := xhat y' i with hu'def
  set dd := u' - u with hdd
  have feasU : ∀ (z : LeiBR.Sync.Profile n) (hz : G.Feasible z) (w : LeiBR.Sync.Strat n i), w ∈ G.X i →
      G.Feasible (Function.update z i w) := by
    intro z hz w hw j
    by_cases h : j = i
    · subst h; simpa using hw
    · rw [Function.update_of_ne h]; exact hz j
  set P := Function.update y i u with hPdef
  set P' := Function.update y' i u' with hP'def
  have hP : P ∈ S := feasU y hy u hu
  have hP' : P' ∈ S := feasU y' hy' u' hu'
  have foc1 := foc G hA1 hxhat hUo hSU i hf y hy u' hu'
  have foc2 := foc G hA1 hxhat hUo hSU i hf y' hy' u hu
  rw [← hudef] at foc1
  rw [← hu'def] at foc2
  obtain ⟨Q, hQ, hmv⟩ := mvt hUo hf hScv hSU hP hP' (Pi.single i dd)
  have hneg : (Pi.single i (u - u') : LeiBR.Sync.Profile n) = -Pi.single i dd := by
    rw [hdd, ← Pi.single_neg, neg_sub]
  rw [hneg, map_neg] at foc2
  -- the key inequality
  have key : fderiv ℝ (fderiv ℝ (G.f i)) Q (P' - P) (Pi.single i dd) ≤
      -mu * ‖dd‖ ^ 2 + mu * inner ℝ (y' i - y i) dd := by
    rw [← hmv]
    have e1 : inner ℝ (u' - y' i) (u - u') = - inner ℝ (u' - y' i) dd := by
      rw [hdd, ← inner_neg_right, neg_sub]
    have e2 : inner ℝ (u - y i) dd - inner ℝ (u' - y' i) dd = -‖dd‖ ^ 2 + inner ℝ (y' i - y i) dd := by
      rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, ← inner_neg_left, ← inner_add_left]
      congr 1; rw [hdd]; abel
    rw [e1] at foc2
    nlinarith
  -- expand the Hessian along the blocks
  have hsym := symmD2 hUo hf (hSU hQ)
  have hexp : fderiv ℝ (fderiv ℝ (G.f i)) Q (P' - P) (Pi.single i dd) =
      ∑ j, hessBlock (G.f i) Q i j dd ((P' - P) j) := by
    conv_lhs => rw [← Finset.univ_sum_single (P' - P)]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsym, hess_eq]
  have hΔ : ∀ j, j ≠ i → (P' - P) j = y' j - y j := by
    intro j hj
    simp [hPdef, hP'def, Function.update_of_ne hj]
  have hΔi : (P' - P) i = dd := by simp [hPdef, hP'def, hdd]
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hΔi] at key
  -- ζ facts
  have hzmin_set : ∀ r ∈ {r : ℝ | ∃ x, G.Feasible x ∧ ∃ v : LeiBR.Sync.Strat n i, ‖v‖ = 1 ∧
      r = hessBlock (G.f i) x i i v v}, 0 ≤ r := by
    rintro r ⟨x, hx, v, -, rfl⟩
    rw [hess_eq]; exact psd G hA1 hUo hSU i hf x hx v
  have hzmin0 : 0 ≤ zetaMin G i := Real.sInf_nonneg hzmin_set
  have hzmax0 : ∀ j, 0 ≤ zetaMax G i j := by
    intro j; unfold zetaMax
    refine Real.sSup_nonneg fun r hr => ?_
    obtain ⟨x, -, rfl⟩ := hr
    exact ContinuousLinearMap.opNorm_nonneg _
  have hzmax_bdd : ∀ j, BddAbove {r : ℝ | ∃ x, G.Feasible x ∧ r = ‖hessBlock (G.f i) x i j‖} := by
    intro j
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (G.f i)) U := hf.fderiv_of_isOpen hUo (by norm_num)
    have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ (G.f i))) U := h1.continuousOn_fderiv_of_isOpen hUo le_rfl
    obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ (G.f i))) (h2.mono hSU)
    refine ⟨max B 0, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact hess_bound x i j _ (le_max_right _ _) ((hB x hx).trans (le_max_left _ _))
  -- lower bound on the diagonal term
  have hdiag : zetaMin G i * ‖dd‖ ^ 2 ≤ hessBlock (G.f i) Q i i dd dd := by
    rcases eq_or_ne dd 0 with h0 | h0
    · rw [h0]; simp
    · have hn : 0 < ‖dd‖ := norm_pos_iff.2 h0
      set v := ‖dd‖⁻¹ • dd with hv
      have hv1 : ‖v‖ = 1 := by rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have hle : zetaMin G i ≤ hessBlock (G.f i) Q i i v v :=
        csInf_le ⟨0, hzmin_set⟩ ⟨Q, hQ, v, hv1, rfl⟩
      have hdv : dd = ‖dd‖ • v := by rw [hv, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h' : hessBlock (G.f i) Q i i (‖dd‖ • v) (‖dd‖ • v) = ‖dd‖ ^ 2 * hessBlock (G.f i) Q i i v v := by
        simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]; ring
      have : hessBlock (G.f i) Q i i dd dd = ‖dd‖ ^ 2 * hessBlock (G.f i) Q i i v v := by
        rw [← h', ← hdv]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
  -- bounds on the off-diagonal terms
  have hoff : ∀ j ∈ Finset.univ.erase i,
      -(zetaMax G i j * ‖dd‖ * ‖y' j - y j‖) ≤ hessBlock (G.f i) Q i j dd ((P' - P) j) := by
    intro j hj
    rw [hΔ j (Finset.ne_of_mem_erase hj)]
    have h1 := (hessBlock (G.f i) Q i j).le_opNorm₂ dd (y' j - y j)
    have h2 : ‖hessBlock (G.f i) Q i j‖ ≤ zetaMax G i j := le_csSup (hzmax_bdd j) ⟨Q, hQ, rfl⟩
    have h3 : ‖hessBlock (G.f i) Q i j‖ * ‖dd‖ * ‖y' j - y j‖ ≤ zetaMax G i j * ‖dd‖ * ‖y' j - y j‖ := by
      gcongr
    have h4 := neg_abs_le (hessBlock (G.f i) Q i j dd (y' j - y j))
    rw [← Real.norm_eq_abs] at h4
    linarith
  have hsumoff := Finset.sum_le_sum hoff
  rw [Finset.sum_neg_distrib] at hsumoff
  have hcs : inner ℝ (y' i - y i) dd ≤ ‖y' i - y i‖ * ‖dd‖ := real_inner_le_norm _ _
  set R := mu * ‖y' i - y i‖ + ∑ j ∈ Finset.univ.erase i, zetaMax G i j * ‖y' j - y j‖ with hR
  have hR0 : 0 ≤ R := add_nonneg (by positivity)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hzmax0 j) (norm_nonneg _))
  have hsum_eq : ∑ j ∈ Finset.univ.erase i, zetaMax G i j * ‖dd‖ * ‖y' j - y j‖ =
      ‖dd‖ * ∑ j ∈ Finset.univ.erase i, zetaMax G i j * ‖y' j - y j‖ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  have hmain : (mu + zetaMin G i) * ‖dd‖ ^ 2 ≤ ‖dd‖ * R := by
    rw [hR, mul_add, ← hsum_eq]
    nlinarith
  have hpos : 0 < mu + zetaMin G i := by linarith
  have hgoal : ‖dd‖ ≤ R / (mu + zetaMin G i) := by
    rw [le_div_iff₀ hpos]
    rcases (norm_nonneg dd).eq_or_lt with h0 | h0
    · rw [← h0]; simp; exact hR0
    · nlinarith
  have hrhs : ∑ j, Gamma G mu i j * ‖y' j - y j‖ = R / (mu + zetaMin G i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hR, add_div, Finset.sum_div]
    congr 1
    · simp [Gamma]; ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hji : i ≠ j := fun h => Finset.ne_of_mem_erase hj h.symm
      simp [Gamma, hji]; ring
  rw [hrhs]
  exact hgoal
