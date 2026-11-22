-- Prove2me | solution 1 for NoHair.Weyl.kerr_radial_quadratures
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:24:43.271879+00:00
-- url     : https://prove2.me/submissions/70b761ae-2b9c-4e0a-9aaf-6d305ac259cf

import Theorems.Thm_NoHair_Weyl_kerr_radial_rate_identities

noncomputable section

open NoHair NoHair.Weyl Set Filter Topology

/-- Smooth compactified radial quantities, with t equal to the inverse Weyl radius. -/
private def barU (k z t : ℝ) :=
  (Real.sqrt (1+(t*(z-k))^2)+Real.sqrt (1+(t*(z+k))^2))/2
private def barR (m k z t : ℝ) := m*t+barU k z t
private def barC (k z t : ℝ) := t*z/barU k z t
private def barN (m a k z t : ℝ) :=
  let r := barR m k z t
  let c := barC k z t
  (r^2+a^2*t^2)*(r^2+a^2*c^2*t^2)+2*m*r*a^2*(1-c^2)*t^3
private def barD (k z t : ℝ) := (barU k z t)^2-k^2*(barC k z t)^2*t^2
private def barW (m a k z t : ℝ) := (-(2*m*a*barR m k z t*t^3))/barN m a k z t
private def barH (m a k z t : ℝ) := (1-(barC k z t)^2)*barN m a k z t/barD k z t

private theorem focal_gaps (k z t : ℝ) :
    |t*z| < barU k z t ∧ |t*k| < barU k z t := by
  have side (b : ℝ) : |b| < Real.sqrt (1+b^2) := by
    rw [← Real.sqrt_sq_eq_abs b]
    exact Real.sqrt_lt_sqrt (sq_nonneg b) (by linarith)
  have h := abs_add_le (t*(z-k)) (t*(z+k))
  rw [show t*(z-k)+t*(z+k) = 2*(t*z) by ring, abs_mul, abs_of_pos (by norm_num : 0<(2:ℝ))] at h
  have j' : |t*(z+k)-t*(z-k)| ≤ |t*(z+k)|+|t*(z-k)| := abs_sub _ _
  rw [show t*(z+k)-t*(z-k) = 2*(t*k) by ring,abs_mul,abs_of_pos (by norm_num : 0<(2:ℝ))] at j'
  unfold barU
  constructor <;> linarith [side (t*(z-k)),side (t*(z+k))]

private theorem compact_pos (m a k z t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) :
    0 < barU k z t ∧ 0 < 1-(barC k z t)^2 ∧ 0 < barN m a k z t ∧ 0 < barD k z t := by
  obtain ⟨hz,hk⟩ := focal_gaps k z t
  have hU := (abs_nonneg _).trans_lt hz
  have hcos : |barC k z t| < 1 := by
    rw [barC,abs_div,abs_of_pos hU,div_lt_iff₀ hU,one_mul]
    exact hz
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hcos
  have hs : 0 < 1-(barC k z t)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hhi) (show 0 < 1+barC k z t by linarith)]
  have hr : 0 < barR m k z t := add_pos_of_nonneg_of_pos (mul_nonneg hm.le ht) hU
  have hsq : (t*k)^2 < (barU k z t)^2 := by
    obtain ⟨hl,hh⟩ := abs_lt.mp hk
    nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < barU k z t+t*k by linarith)]
  refine ⟨hU,hs,?_,?_⟩
  · unfold barN
    positivity
  · unfold barD
    nlinarith only [hsq,mul_nonneg (sq_nonneg (t*k)) hs.le]

private theorem compact_smooth (m a k z t : ℝ) (hm : 0 < m) (ht : 0 ≤ t) :
    ContDiffAt ℝ 1 (barW m a k z) t ∧
    ContDiffAt ℝ 1 (fun b => Real.log (barH m a k z b)/2) t := by
  obtain ⟨hu,hs,hn,hd⟩ := compact_pos m a k z t hm ht
  have hU : ContDiffAt ℝ 1 (barU k z) t := by unfold barU; fun_prop (disch := positivity)
  have hR : ContDiffAt ℝ 1 (barR m k z) t := by unfold barR; fun_prop
  have hC : ContDiffAt ℝ 1 (barC k z) t := by unfold barC; fun_prop (disch := exact hu.ne')
  have hN : ContDiffAt ℝ 1 (barN m a k z) t := by unfold barN; fun_prop
  have hD : ContDiffAt ℝ 1 (barD k z) t := by unfold barD; fun_prop
  have hH : ContDiffAt ℝ 1 (barH m a k z) t := by unfold barH; fun_prop (disch := exact hd.ne')
  have hval : 0 < barH m a k z t := div_pos (mul_pos hs hn) hd
  constructor
  · unfold barW
    fun_prop (disch := exact hn.ne')
  · fun_prop (disch := exact hval.ne')

private theorem compactified_values (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) (z s : ℝ) :
    let k := Real.sqrt (m^2-a^2)
    let t := Real.exp (-s)
    barW m a k z t = kerrWeylShift m a (s,z) ∧
      Real.log (barH m a k z t)/2 = Real.log (kerrWeylScale m a (s,z))/2-s := by
  let k := Real.sqrt (m^2-a^2)
  let t := Real.exp (-s)
  let u := prolateRadius k (s,z)
  let r := m+u
  let c := z/u
  have ht : 0 < t := Real.exp_pos _
  have he : t^2*Real.exp (2*s)=1 := by
    dsimp [t]
    rw [two_mul,Real.exp_add,Real.exp_neg]
    field_simp
  have side (b : ℝ) : Real.sqrt (1+(t*b)^2) = t*Real.sqrt (Real.exp (2*s)+b^2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg ht.le (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (by positivity),mul_pow t (Real.sqrt (Real.exp (2*s)+b^2)),Real.sq_sqrt (by positivity)]
    nlinarith only [he]
  have hU : barU k z t = t*u := by
    dsimp [barU,u,prolateRadius]
    rw [side,side]
    ring
  have hr : barR m k z t = t*r := by dsimp [barR,r]; rw [hU]; ring
  have hc : barC k z t = c := by
    change t*z/barU k z t=z/u
    rw [hU,mul_div_mul_left _ _ ht.ne']
  have hk : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  let N := kerrAxialNumerator m a r c
  let D := (r-m)^2-(m^2-a^2)*c^2
  have hN : barN m a k z t=t^4*N := by unfold barN N kerrAxialNumerator; rw [hr,hc]; ring
  have hD : barD k z t=t^2*D := by unfold barD D; rw [hU,hc,hk]; dsimp [r]; ring
  obtain ⟨_,hs,hNp,hDp⟩ := compact_pos m a k z t hm.1 ht.le
  have n0 : N ≠ 0 := by intro hh; rw [hN,hh,mul_zero] at hNp; exact lt_irrefl _ hNp
  have d0 : D ≠ 0 := by intro hh; rw [hD,hh,mul_zero] at hDp; exact lt_irrefl _ hDp
  have hval : barH m a k z t = t^2*kerrWeylScale m a (s,z) := by
    change (1-(barC k z t)^2)*barN m a k z t/barD k z t=t^2*((1-c^2)*N/D)
    rw [hc,hN,hD]
    field_simp [ht.ne',d0]
    <;> ring
  constructor
  · change (-(2*m*a*barR m k z t*t^3))/barN m a k z t= -(2*m*a*r)/N
    rw [hr,hN]
    field_simp [ht.ne',n0] <;> ring
  · change Real.log (barH m a k z t)/2=_
    rw [hval,Real.log_mul (pow_ne_zero 2 ht.ne') (kerr_radial_rate_identities m a hm s z).1.ne',
      Real.log_pow,show Real.log t = -s from Real.log_exp _]
    ring

open Set Filter Topology MeasureTheory

private theorem compact_radial_integral (F rate : ℝ → ℝ) (F0 : F 0=0)
    (smooth : ∀ t : ℝ, 0 ≤ t → ContDiffAt ℝ 1 F t)
    (hd : ∀ s : ℝ, HasDerivAt (fun x => F (Real.exp (-x))) (rate s) s) (a : ℝ) :
    IntegrableOn rate (Ioi a) ∧ (∫ x in Ioi a, rate x) = -F (Real.exp (-a)) := by
  let T := fun s : ℝ => Real.exp (-s)
  have hT (s : ℝ) : HasDerivAt T (-T s) s := by
    convert ((hasDerivAt_id' s).neg.exp) using 1 <;> simp [T]
  have limT : Tendsto T atTop (𝓝 0) := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hcT : Continuous T := by unfold T; fun_prop
  have hder (t : ℝ) (ht : 0 ≤ t) : ContinuousAt (deriv F) t :=
    ((smooth t ht).derivWithin (m:=0) (by norm_num)).continuousAt
  have rate_eq : rate = fun s => deriv F (T s)*(-T s) := funext fun s =>
    (hd s).unique (((smooth (T s) (Real.exp_pos _).le).differentiableAt (by norm_num)).hasDerivAt.comp s (hT s))
  have hcont : Continuous rate := by
    rw [rate_eq]
    exact continuous_iff_continuousAt.2 fun s =>
      ((hder (T s) (Real.exp_pos _).le).comp hcT.continuousAt).mul hcT.neg.continuousAt
  have hTpos (s : ℝ) : 0 < T s := Real.exp_pos _
  have intT : IntegrableOn T (Ioi a) := by
    have h := integrableOn_Ioi_deriv_of_nonpos' (a:=a) (fun s _ => hT s) (fun s _ => neg_nonpos.mpr (hTpos s).le) limT
    simpa using h.neg
  let K := Icc (0:ℝ) (T a)
  have hk : ContinuousOn (fun t => |deriv F t|) K := fun t ht => (hder t ht.1).abs.continuousWithinAt
  obtain ⟨b,_,hb⟩ := isCompact_Icc.exists_isMaxOn (show K.Nonempty from ⟨0,le_rfl,(hTpos a).le⟩) hk
  have hi : IntegrableOn rate (Ioi a) := by
    apply (intT.const_mul |deriv F b|).mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=a))] with s hs
    have hsK : T s ∈ K := ⟨(hTpos s).le, Real.exp_le_exp.mpr (neg_le_neg hs.out.le)⟩
    rw [Real.norm_eq_abs,rate_eq,abs_mul,abs_neg,abs_of_pos (hTpos s)]
    exact mul_le_mul_of_nonneg_right ((isMaxOn_iff.mp hb) (T s) hsK) (hTpos s).le
  have limit : Tendsto (fun x => F (Real.exp (-x))) atTop (𝓝 0) := by
    simpa only [F0,Function.comp_def,T] using ((smooth 0 le_rfl).continuousAt.tendsto.comp limT)
  exact ⟨hi,by simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hd s) hi limit⟩

open MeasureTheory

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    HasRadialQuadratures (kerrErnst m a) ∧ ∀ p : OrbitPoint,
      angularShift (kerrErnst m a) p = kerrWeylShift m a p ∧
      Real.exp (2*conformalExponent (kerrErnst m a) p) = kerrWeylScale m a p := by
  let k := Real.sqrt (m^2-a^2)
  have ray (a₀ z : ℝ) :
      let f := fun t : ℝ => shiftRate (kerrErnst m a) (t,z)
      let g := fun t : ℝ => conformalRate (kerrErnst m a) (t,z)
      IntegrableOn f (Ioi a₀) ∧ IntegrableOn g (Ioi a₀) ∧
      (∫ t in Ioi a₀, f t) = -kerrWeylShift m a (a₀,z) ∧
      (∫ t in Ioi a₀, g t) = -(Real.log (kerrWeylScale m a (a₀,z))/2-a₀) := by
    have e₁ : (fun t => barW m a k z (Real.exp (-t))) = fun t => kerrWeylShift m a (t,z) :=
      funext fun t => (compactified_values m a hm z t).1
    have e₂ : (fun t => Real.log (barH m a k z (Real.exp (-t)))/2) =
        fun t => Real.log (kerrWeylScale m a (t,z))/2-t := funext fun t => (compactified_values m a hm z t).2
    have zW : barW m a k z 0 = 0 := by simp [barW]
    have zH : Real.log (barH m a k z 0)/2=0 := by norm_num [barH,barN,barD,barR,barC,barU]
    have h₁ := compact_radial_integral (barW m a k z) _ zW (fun t ht => (compact_smooth m a k z t hm.1 ht).1)
      (fun t => e₁ ▸ (kerr_radial_rate_identities m a hm t z).2.1) a₀
    have h₂ := compact_radial_integral (fun t => Real.log (barH m a k z t)/2) _ zH
      (fun t ht => (compact_smooth m a k z t hm.1 ht).2)
      (fun t => e₂ ▸ (kerr_radial_rate_identities m a hm t z).2.2) a₀
    exact ⟨h₁.1,h₂.1,h₁.2.trans (congrArg Neg.neg (congrFun e₁ a₀)),
      h₂.2.trans (congrArg Neg.neg (congrFun e₂ a₀))⟩
  constructor
  · intro p
    exact ⟨(ray p.1 p.2).1,(ray p.1 p.2).2.1⟩
  · rintro ⟨s,z⟩
    obtain ⟨_,_,hw,hh⟩ := ray s z
    dsimp only at hw hh
    constructor
    · unfold angularShift
      rw [hw,neg_neg]
    · unfold conformalExponent
      rw [hh,show 2*(s- -(Real.log (kerrWeylScale m a (s,z))/2-s)) =
          Real.log (kerrWeylScale m a (s,z)) by ring,Real.exp_log (kerr_radial_rate_identities m a hm s z).1]
