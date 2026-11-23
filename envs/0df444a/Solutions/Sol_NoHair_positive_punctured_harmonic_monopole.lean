-- Prove2me | solution 1 for NoHair.positive_punctured_harmonic_monopole
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:13:44.905081+00:00
-- url     : https://prove2.me/submissions/754a39a4-1d61-451f-994c-dc76e3bba591

import Theorems.Thm_HunterPDE_Harmonic_strong_maximum_principle
import Theorems.Thm_YukawaPotential_yukawaPotential_laplacian

import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection

open Set Metric Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

private abbrev X := EuclideanSpace ℝ (Fin 3)
private abbrev puncture : Set X := {0}ᶜ

private lemma harmonic_inverse : HarmonicOnNhd (fun x : X => 1 / ‖x‖) puncture := by
  have h : HarmonicOnNhd (fun x : X => -(1 / ‖x‖)) puncture := by
    intro x hx
    change x ≠ 0 at hx
    refine ⟨(contDiffAt_const.div (contDiffAt_norm ℝ hx) (norm_ne_zero_iff.mpr hx)).neg, ?_⟩
    filter_upwards [eventually_ne_nhds hx] with y hy
    simpa [YukawaPotential.yukawaPotential, neg_div] using
      YukawaPotential.yukawaPotential_laplacian 1 0 0 y hy
  have e : -(fun x : X => -(1 / ‖x‖)) = (fun x : X => 1 / ‖x‖) := by
    funext x
    simp only [Pi.neg_apply, neg_neg]
  exact e ▸ h.neg

private lemma compact_maximum {f : X → ℝ} {K S : Set X} (hK : IsCompact K) (h₀ : (0:X) ∉ K)
    (hcont : ContinuousOn f K) (hS : IsOpen S) (hf : HarmonicOnNhd f S)
    (into : ∀ y ∈ S, 0 < f y → y ∈ K) (back : ∀ y ∈ K, 0 < f y → y ∈ S) :
    ∀ x ∈ S, f x ≤ 0 := by
  intro x hx
  by_contra! hpos
  obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn ⟨x,into x hx hpos⟩ hcont
  have hp : 0 < f z := hpos.trans_le (hm (into x hx hpos))
  let L := K ∩ f ⁻¹' Ici (f z)
  have closed : IsClosed L := (hcont.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK (f z)).isClosed
  have popen : IsOpen (S ∩ f ⁻¹' Ioi 0) := hf.contDiffOn.continuousOn.isOpen_inter_preimage hS isOpen_Ioi
  have op : IsOpen L := by
    apply Metric.isOpen_iff.mpr
    intro a ha
    have haK : a ∈ K := ha.1
    have haM : f a = f z := le_antisymm (hm haK) ha.2
    have hap : 0 < f a := haM ▸ hp
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp popen a ⟨back a haK hap,hap⟩
    refine ⟨r,hr,?_⟩
    have hball : HarmonicOnNhd f (ball a r) := fun y hy => hf y (hsub hy).1
    have subharm : HunterPDE.Harmonic.IsSubharmonicOn (ball a r) f :=
      ⟨hball.contDiffOn, fun y hy => le_of_eq ((hball y hy).2.self_of_nhds.symm)⟩
    have hac : a ∈ ball a r := mem_ball_self hr
    obtain ⟨c,hc⟩ := HunterPDE.Harmonic.strong_maximum_principle isOpen_ball
      (convex_ball a r).isPreconnected subharm
      ⟨a,hac,fun y hy => (hm (into y (hsub hy).1 (hsub hy).2)).trans_eq haM.symm⟩
    intro y hy
    exact ⟨into y (hsub hy).1 (hsub hy).2,by
      change f z ≤ f y
      rw [← haM,hc a hac,hc y hy]⟩
  have allL : L=univ := IsClopen.eq_univ ⟨closed,op⟩ ⟨z,hz,show f z ≤ f z from le_rfl⟩
  have zeroL : (0:X) ∈ L := allL ▸ mem_univ _
  exact h₀ zeroL.1

private lemma lap_affine (e : X ≃ᵃⁱ[ℝ] X) (U : X → ℝ) (x : X) :
    (Δ (U ∘ e)) x = (Δ U) (e x) := by
  let l := e.linearIsometryEquiv
  let B := stdOrthonormalBasis ℝ X
  have representation (y:X) : e y=l y+e 0 := by
    simpa only [vadd_eq_add,add_zero,l] using e.map_vadd (0:X) y
  let v := fun y:X => U (y+e 0)
  have funEq : U ∘ e = v ∘ l := by funext y; change U (e y) = U (l y+e 0); rw [representation]
  have jets : iteratedFDeriv ℝ 2 (v ∘ l) x =
      (iteratedFDeriv ℝ 2 v (l x)).compContinuousLinearMap (fun _ => l.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa only [preimage_univ,iteratedFDerivWithin_univ,LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right v uniqueDiffOn_univ (x:=x) (mem_univ _) 2
  rw [funEq,laplacian_eq_iteratedFDeriv_orthonormalBasis (v ∘ l) B,
    laplacian_eq_iteratedFDeriv_orthonormalBasis U (B.map l)]
  dsimp only
  rw [jets,representation x]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,v,iteratedFDeriv_comp_add_right]
  congr 1
  funext j
  fin_cases j <;> rfl

private lemma harmonic_affine (e : X ≃ᵃⁱ[ℝ] X) {U : X → ℝ} {x:X} (hu : HarmonicAt U (e x)) :
    HarmonicAt (U ∘ e) x := by
  have ec : ContDiff ℝ 2 (fun y:X => e y) := by
    have he : (fun y:X => e y) = fun y => e.linearIsometryEquiv y+e 0 := by
      funext y
      simpa only [vadd_eq_add,add_zero] using e.map_vadd (0:X) y
    rw [he]
    exact e.linearIsometryEquiv.toContinuousLinearEquiv.contDiff.add contDiff_const
  refine ⟨hu.1.comp x ec.contDiffAt,?_⟩
  filter_upwards [e.continuous.continuousAt.tendsto.eventually hu.2] with y hy
  change (Δ (U ∘ e)) y = 0
  rw [lap_affine]; exact hy

private instance perpBisectorInhabited (x y : X) : Nonempty (AffineSubspace.perpBisector x y) :=
  ⟨⟨_, AffineSubspace.midpoint_mem_perpBisector x y⟩⟩

private lemma reflect_swaps (x y:X) :
    (EuclideanGeometry.reflection (AffineSubspace.perpBisector x y)) x = y := by
  let s := AffineSubspace.perpBisector x y
  let c := midpoint ℝ x y
  have hmem : c ∈ s := AffineSubspace.midpoint_mem_perpBisector x y
  have hr := EuclideanGeometry.reflection_apply_of_mem s x hmem
  have negDir : s.direction.reflection (y -ᵥ x) = -(y -ᵥ x) := by
    apply Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
    rw [show s.direction = _ from AffineSubspace.direction_perpBisector x y]
    exact (ℝ ∙ (y -ᵥ x)).le_orthogonal_orthogonal (Submodule.mem_span_singleton_self _)

  have hd : x -ᵥ c = - ((⅟2:ℝ) • (y -ᵥ x)) := by
    dsimp only [c]
    rw [left_vsub_midpoint, ← smul_neg,neg_vsub_eq_vsub_rev]
  have hd' : y -ᵥ c = (⅟2:ℝ) • (y -ᵥ x) := by
    dsimp only [c]
    rw [right_vsub_midpoint]
  rw [hd,map_neg,map_smul,negDir,
    smul_neg,neg_neg,← hd'] at hr
  simpa only [c,vsub_vadd] using hr

private lemma nearer (U:X→ℝ) (hh:HarmonicOnNhd U puncture) (hn:∀ x, x≠0 → 0≤U x)
    (hf : ∀ ε:ℝ, 0<ε → ∃ L:ℝ, ∀ x:X, L<‖x‖ → |U x-1|≤ε)
    {x y:X} (hx:x≠0) (hxy:‖x‖<‖y‖) : U y ≤ U x := by
  let s := AffineSubspace.perpBisector x y
  let e := EuclideanGeometry.reflection s
  have ex : e x=y := reflect_swaps x y
  have ey : e y=x := ex ▸ EuclideanGeometry.reflection_reflection s x
  let near := fun z:X => dist z x ≤ dist z y
  have hne (z:X) (h:near z) : e z ≠ 0 := by
    intro zer
    have dx := e.dist_map z x
    have dy := e.dist_map z y
    rw [zer,ex,dist_zero_left] at dx
    rw [zer,ey,dist_zero_left] at dy
    change dist z x ≤ dist z y at h
    linarith
  have e0 : e 0 ≠ 0 := hne 0 (by simpa only [near,dist_zero_left] using hxy.le)
  have ct : ContinuousAt (U ∘ e) 0 := (hh _ e0).1.continuousAt.comp e.continuous.continuousAt
  by_contra! contra
  let w := fun z:X => U (e z)-U z
  have wx : 0<w x := by dsimp only [w]; rw [ex]; linarith
  have factor : 0<1+1/‖x‖ := by positivity
  let ε := w x /(2*(1+1/‖x‖))
  have ep : 0<ε := div_pos wx (mul_pos (by norm_num) factor)
  let f := fun z:X => w z-ε*(1+1/‖z‖)
  have fx : 0<f x := by
    have h : ε*(1+1/‖x‖)=w x/2 := by dsimp only [ε]; field_simp [factor.ne']
    dsimp only [f]; rw [h]; linarith
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp ct 1 zero_lt_one
  let C := |U (e 0)|+2
  have cp : 0<C := by dsimp [C]; positivity
  let d := min δ (ε/C)
  have dp : 0<d := lt_min hδ (div_pos ep cp)
  have small (z:X) (hnz:0<‖z‖) (hd:‖z‖<d) : f z ≤ 0 := by
    have h := hbound (show dist z 0 < δ by simpa only [dist_zero_right] using (lt_min_iff.mp hd).1)
    change dist (U (e z)) (U (e 0)) < 1 at h
    rw [Real.dist_eq] at h
    have wz : w z ≤ C := by
      dsimp only [w,C]
      linarith only [(abs_lt.mp h).2,hn z (norm_pos_iff.mp hnz),le_abs_self (U (e 0))]
    have hz := (lt_div_iff₀ cp).mp (lt_min_iff.mp hd).2
    have hc : C ≤ ε/‖z‖ := (le_div_iff₀ hnz).mpr (by linarith)
    have id : ε*(1+1/‖z‖)=ε+ε/‖z‖ := by ring
    dsimp only [f]; rw [id]; linarith
  obtain ⟨N,hN⟩ := hf (ε/2) (half_pos ep)
  let L := N+‖e 0‖
  have large (z:X) (hz:L<‖z‖) : f z ≤ 0 := by
    have hzz : ‖z‖ ≤ ‖e z‖+‖e 0‖ := by
      simpa only [e.dist_map,dist_zero_right] using
        (calc dist (e z) (e 0) ≤ ‖e z‖+‖e 0‖ := dist_le_norm_add_norm _ _)
    have hg := hN z (by dsimp only [L] at hz; linarith only [norm_nonneg (e 0),hz])
    have hg' := hN (e z) (by dsimp only [L] at hz; linarith)
    have wz : w z ≤ ε := by dsimp only [w]; linarith only [(abs_le.mp hg).1,(abs_le.mp hg').2]
    have h := mul_nonneg ep.le (show 0 ≤ 1/‖z‖ by positivity)
    dsimp only [f]; linarith
  let S : Set X := {z | z≠0} ∩ {z | dist z x < dist z y}
  let K : Set X := (closedBall 0 L ∩ {z | d≤‖z‖}) ∩ {z | near z}
  have hk : IsCompact K := ((isCompact_closedBall (0:X) L).inter_right (isClosed_le continuous_const continuous_norm)).inter_right
    (isClosed_le (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
  have hs : IsOpen S := isOpen_compl_singleton.inter (isOpen_lt
    (continuous_id.dist continuous_const) (continuous_id.dist continuous_const))
  have reg (z:X) (nz:z≠0) (nn:near z) : HarmonicAt f z :=
    ((harmonic_affine e (hh _ (hne z nn))).sub (hh z nz)).sub
      (((harmonicAt_const 1).add (harmonic_inverse z nz)).const_smul (c:=ε))
  have cont : ContinuousOn f K := fun z hz =>
    (reg z (norm_pos_iff.mp (dp.trans_le hz.1.2)) hz.2).1.continuousAt.continuousWithinAt
  have incl (z:X) (hz:z∈S) (hp:0<f z) : z∈K := by
    refine ⟨⟨?_,?_⟩, (show dist z x ≤ dist z y from (show dist z x < dist z y from hz.2).le)⟩
    · apply mem_closedBall.mpr
      rw [dist_zero_right]
      exact le_of_not_gt (fun hh' => hp.not_ge (large z hh'))
    · exact le_of_not_gt (fun h => hp.not_ge (small z (norm_pos_iff.mpr hz.1) h))
  have back (z:X) (hz:z∈K) (hp:0<f z) : z∈S := by
    refine ⟨norm_pos_iff.mp (dp.trans_le hz.1.2), ?_⟩
    change dist z x < dist z y
    apply lt_of_le_of_ne (show dist z x ≤ dist z y from hz.2)
    intro eq
    have fix : e z = z := (EuclideanGeometry.reflection_eq_self_iff z).mpr
      (AffineSubspace.mem_perpBisector_iff_dist_eq.mpr eq)
    have bound : 0 ≤ ε*(1+1/‖z‖) := by positivity
    dsimp only [f,w] at hp; rw [fix] at hp; linarith
  have no : (0:X)∉K := fun h => (not_lt_of_ge (show d≤‖(0:X)‖ from h.1.2))
    (by simpa only [norm_zero] using dp)
  have hzero := compact_maximum hk no cont hs (fun z hz => reg z hz.1 (show dist z x ≤ dist z y from (show dist z x < dist z y from hz.2).le)) incl back
  have neq : x≠y := fun he => (lt_irrefl _ (he ▸ hxy))
  exact fx.not_ge (hzero x ⟨hx,by simpa [dist_pos.mpr neq] using dist_pos.mpr neq⟩)

private lemma sphere_constant (U : X → ℝ) (hh : HarmonicOnNhd U puncture)
    (hn : ∀ x, x ≠ 0 → 0 ≤ U x)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x : X, L < ‖x‖ → |U x - 1| ≤ ε)
    {x y : X} (hx : x ≠ 0) (hy : y ≠ 0) (heq : ‖x‖ = ‖y‖) : U x = U y := by
  have side (a b : X) (ha : a ≠ 0) (hb : b ≠ 0) (eq : ‖a‖ = ‖b‖) : U b ≤ U a := by
    have hb' : ContinuousAt U ((1:ℝ) • b) := by simpa using (hh b hb).1.continuousAt
    have cont : ContinuousAt (fun t : ℝ => U (t • b)) 1 :=
      ContinuousAt.comp (f := fun t : ℝ => t • b) hb' (continuousAt_id.smul continuousAt_const)
    have h : ∀ᶠ t : ℝ in 𝓝[>] (1:ℝ), U (t • b) ≤ U a := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change (1:ℝ) < t at ht
      apply nearer U hh hn hf ha
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans ht), eq]
      simpa only [one_mul] using mul_lt_mul_of_pos_right ht (norm_pos_iff.mpr hb)
    simpa only [one_smul] using le_of_tendsto (cont.tendsto.mono_left nhdsWithin_le_nhds) h
  exact le_antisymm (side y x hy hx heq.symm) (side x y hx hy heq)

private lemma outside_nonpos {f : X → ℝ} (hh : HarmonicOnNhd f puncture)
    {a : ℝ} (ha : 0 < a) (boundary : ∀ y, ‖y‖ = a → f y = 0)
    (far : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ y, L < ‖y‖ → f y ≤ ε) :
    ∀ x, a < ‖x‖ → f x ≤ 0 := by
  intro x hx
  by_contra! hpos
  let ε := f x / 2
  have ep : 0 < ε := half_pos hpos
  let g := fun z => f z - ε
  obtain ⟨L, hL⟩ := far ε ep
  let S : Set X := {z | a < ‖z‖}
  let K : Set X := closedBall 0 L ∩ {z | a ≤ ‖z‖}
  have hk : IsCompact K := (isCompact_closedBall (0 : X) L).inter_right
    (isClosed_le continuous_const continuous_norm)
  have ns : (0 : X) ∉ K := fun hz =>
    (not_lt_of_ge (show a ≤ ‖(0:X)‖ from hz.2)) (by simpa only [norm_zero] using ha)
  have reg (z : X) (hz : a ≤ ‖z‖) : HarmonicAt g z :=
    (hh z (norm_pos_iff.mp (ha.trans_le hz))).sub (harmonicAt_const ε)
  have cont : ContinuousOn g K := fun z hz => (reg z hz.2).1.continuousAt.continuousWithinAt
  have hS : IsOpen S := isOpen_lt continuous_const continuous_norm
  have into (z : X) (hz : z ∈ S) (hp : 0 < g z) : z ∈ K := by
    refine ⟨mem_closedBall.mpr ?_, (show a ≤ ‖z‖ from (show a < ‖z‖ from hz).le)⟩
    rw [dist_zero_right]
    by_contra! huge
    have bound := hL z huge
    dsimp only [g] at hp
    linarith
  have back (z : X) (hz : z ∈ K) (hp : 0 < g z) : z ∈ S := by
    change a < ‖z‖
    apply lt_of_le_of_ne (show a ≤ ‖z‖ from hz.2)
    intro eq
    dsimp only [g] at hp
    rw [boundary z eq.symm] at hp
    linarith
  have bound := compact_maximum hk ns cont hS (fun z hz => reg z (show a ≤ ‖z‖ from (show a < ‖z‖ from hz).le)) into back x hx
  dsimp only [g, ε] at bound
  linarith

theorem solution (U : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hh : HarmonicOnNhd U ({0}ᶜ)) (hpos : ∀ x, x ≠ 0 → 0 ≤ U x)
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x, x ≠ 0 → U x = 1 + b / ‖x‖ := by
  let u : X := EuclideanSpace.single (0 : Fin 3) 1
  have un : ‖u‖ = 1 := by simp [u]
  have uz : u ≠ 0 := norm_pos_iff.mp (by rw [un]; norm_num)
  have nr (r : ℝ) (hr : 0 ≤ r) : ‖r • u‖ = r := by
    rw [norm_smul, un, Real.norm_eq_abs, abs_of_nonneg hr, mul_one]
  have outside (a : ℝ) (ha : 0 < a) :
      ∃ b : ℝ, ∀ x, a < ‖x‖ → U x = 1 + b / ‖x‖ := by
    let b := a * (U (a • u) - 1)
    let W := fun x : X => U x - (1 + b * (1 / ‖x‖))
    have hw : HarmonicOnNhd W puncture :=
      hh.sub ((harmonicOnNhd_const 1).add (harmonic_inverse.const_smul (c := b)))
    have boundary (y : X) (hy : ‖y‖ = a) : W y = 0 := by
      have p : 0 < ‖y‖ := hy ▸ ha
      have q : 0 < ‖a • u‖ := by rw [nr a ha.le]; exact ha
      have h := sphere_constant U hh hpos hfar (norm_pos_iff.mp p) (norm_pos_iff.mp q)
        (hy.trans (nr a ha.le).symm)
      dsimp only [W, b]
      rw [hy, h]
      field_simp [ha.ne']
      <;> ring
    have far (ε : ℝ) (he : 0 < ε) : ∃ L : ℝ, ∀ x, L < ‖x‖ → |W x| ≤ ε := by
      obtain ⟨L, hL⟩ := hfar (ε / 2) (half_pos he)
      refine ⟨max L (|b| / (ε / 2)), fun x hx => ?_⟩
      have hsize := (max_lt_iff.mp hx).2
      have hr : 0 < ‖x‖ := (div_nonneg (abs_nonneg b) (half_pos he).le).trans_lt hsize
      have hfrac : |b| / ‖x‖ ≤ ε / 2 := (div_le_iff₀ hr).2 (by
        linarith only [(div_lt_iff₀ (half_pos he)).1 hsize])
      have tri := abs_sub (U x - 1) (b / ‖x‖)
      rw [abs_div, abs_of_pos hr] at tri
      have heq : W x = (U x - 1) - b / ‖x‖ := by dsimp only [W]; ring
      rw [heq]
      linarith only [tri, hfrac, hL x (max_lt_iff.mp hx).1]
    refine ⟨b, fun x hx => ?_⟩
    have pos := outside_nonpos hw ha boundary (fun ε he => by
      obtain ⟨L, hL⟩ := far ε he
      exact ⟨L, fun z hz => (le_abs_self _).trans (hL z hz)⟩) x hx
    have neg := outside_nonpos hw.neg ha (fun z hz => by simp only [Pi.neg_apply, boundary z hz, neg_zero])
      (fun ε he => by
        obtain ⟨L, hL⟩ := far ε he
        exact ⟨L, fun z hz => (neg_le_abs _).trans (hL z hz)⟩) x hx
    change -(W x) ≤ 0 at neg
    dsimp only [W] at pos neg
    rw [show b / ‖x‖ = b * (1 / ‖x‖) by ring]
    linarith
  let b := U u - 1
  have formula (x : X) (hx : x ≠ 0) : U x = 1 + b / ‖x‖ := by
    let a := min ‖x‖ 1 / 2
    have amin : 0 < min ‖x‖ 1 := lt_min (norm_pos_iff.mpr hx) zero_lt_one
    have small : a < min ‖x‖ 1 := half_lt_self amin
    obtain ⟨c, hc⟩ := outside a (half_pos amin)
    have h := hc u (by rw [un]; exact small.trans_le (min_le_right _ _))
    rw [un, div_one] at h
    have eq : c = b := by dsimp only [b]; linarith
    rw [← eq]
    exact hc x (small.trans_le (min_le_left _ _))
  refine ⟨b, ?_, formula⟩
  by_contra! hneg
  let r := -b / 2
  have hr : 0 < r := half_pos (neg_pos.mpr hneg)
  have n : ‖r • u‖ = r := nr r hr.le
  have hn : r • u ≠ 0 := norm_pos_iff.mp (by rw [n]; exact hr)
  have h := formula (r • u) hn
  rw [n] at h
  have eq : b / r = -2 := (div_eq_iff hr.ne').2 (by dsimp only [r]; ring)
  rw [eq] at h
  linarith only [h, hpos _ hn]
