-- Prove2me | solution 1 for ModernOnlineLearning.SaddlePoint.regret_sum_15_26
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:43:41.102203+00:00
-- url     : https://prove2.me/submissions/912c73ea-f03a-45e6-9387-0e625d96c13a

import Definitions.Def_ModernOnlineLearning_SaddlePoint_Setting

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.SaddlePoint

private lemma growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn V lam ψ)
    (θ : E →L[ℝ] ℝ) (x y : E)
    (hx : ModernOnlineLearning.SaddlePoint.IsMinOn V (fun z => ψ z + θ z) x) (hy : y ∈ V) :
    lam / 2 * ‖x - y‖ ^ 2 ≤ ψ y + θ y - (ψ x + θ x) := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖x - y‖ ^ 2) ≤ ψ y + θ y - (ψ x + θ x) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv : (1 - t) • x + t • y ∈ V := hstrong.1 hx.1 hy ha ht.le hab
    have hm := hx.2 _ hv
    have hs := hstrong.2 hx.1 hy ha ht.le hab
    simp only [map_add, map_smul, smul_eq_mul] at hm hs
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖x - y‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
  exact hsegment t ht ht1

private lemma young_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (z : E) (lam : ℝ) (hlam : 0 < lam) :
    g z - lam / 2 * ‖z‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have ho : g z ≤ ‖g‖ * ‖z‖ := by
    have h := g.le_opNorm z
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  apply (le_div_iff₀ (show 0 < 2 * lam by positivity)).mpr
  nlinarith [sq_nonneg (‖g‖ - lam * ‖z‖)]

private lemma telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, (f t - f (t + 1))) = f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

private lemma endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (z : ℕ → E)
    (lam : ℝ) (T : ℕ) (u : E) (hT : 1 ≤ T) (hu : u ∈ V)
    (hstrong : StrongConvexOn V lam ψ) (hrun : IsOptFTRLRun V ψ g z T) :
    (∑ t ∈ Finset.Icc 1 T, g t (z t-u)) ≤ ψ u-ψ (z 1)+
      ∑ t ∈ Finset.Icc 1 T,
        ((g t-g (t-1)) (z t-(if t<T then z (t+1) else u)) -
          lam/2*‖z t-(if t<T then z (t+1) else u)‖^2) := by
  let F : ℕ → E → ℝ := fun t v => ψ v + ∑ i ∈ Finset.Ico 1 t, g i v
  let Z : ℕ → E := fun t => if t ≤ T then z t else u
  have hZ (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : Z t = z t :=
    if_pos (Finset.mem_Icc.mp ht).2
  have hZn (t : ℕ) : Z (t+1) = if t < T then z (t+1) else u := by
    dsimp only [Z]
    congr 1
  have hZmem (t : ℕ) (ht : 1 ≤ t) : Z t ∈ V := by
    by_cases h : t ≤ T
    · simpa only [Z, if_pos h] using (hrun.2 t (Finset.mem_Icc.mpr ⟨ht,h⟩)).1
    · simpa only [Z, if_neg h] using hu
  have hFsucc (t : ℕ) (ht : 1 ≤ t) (v : E) : F (t+1) v = F t v + g t v := by
    dsimp only [F]
    rw [Finset.sum_Ico_succ_top ht]
    ring
  have hstep (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
      F t (Z t) - F (t+1) (Z (t+1)) + g t (z t) ≤
      (g t - g (t-1)) (z t - Z (t+1)) - lam/2 * ‖z t-Z (t+1)‖^2 := by
    let θ : E →L[ℝ] ℝ := g (t-1) + ∑ i ∈ Finset.Ico 1 t, g i
    have hθ (v : E) : θ v = g (t-1) v + ∑ i ∈ Finset.Ico 1 t, g i v := by simp [θ]
    have hm : ModernOnlineLearning.SaddlePoint.IsMinOn V (fun v => ψ v + θ v) (z t) := by
      refine ⟨(hrun.2 t ht).1, ?_⟩
      intro v hv
      have h := (hrun.2 t ht).2 v hv
      simp only [hθ]
      linarith
    have hg := growth V ψ lam hstrong θ (z t) (Z (t+1)) hm (hZmem _ (by omega))
    rw [hθ, hθ] at hg
    have hg' : lam/2 * ‖z t-Z (t+1)‖^2 ≤
        F t (Z (t+1)) + g (t-1) (Z (t+1)) - (F t (z t)+g (t-1) (z t)) := by
      dsimp only [F]
      linarith
    rw [hZ t ht, hFsucc t (Finset.mem_Icc.mp ht).1]
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    linarith
  have hs := Finset.sum_le_sum hstep
  have htel : (∑ t ∈ Finset.Icc 1 T,
      (F t (Z t)-F (t+1) (Z (t+1))+g t (z t))) =
      ψ (z 1)-F (T+1) u + ∑ t ∈ Finset.Icc 1 T, g t (z t) := by
    rw [Finset.sum_add_distrib, telescope (fun t => F t (Z t))]
    simp only [Z, if_pos hT, Nat.not_succ_le_self, if_false]
    simp only [F, Finset.Ico_self, Finset.sum_empty, add_zero]
  rw [htel] at hs
  have hFu : F (T+1) u = ψ u + ∑ t ∈ Finset.Icc 1 T, g t u := by
    simp only [F, Finset.Ico_add_one_right_eq_Icc]
  have hfirst : (∑ t ∈ Finset.Icc 1 T, g t (z t-u)) ≤
      ψ u-ψ (z 1)+(∑ t ∈ Finset.Icc 1 T,
      ((g t-g (t-1)) (z t-Z (t+1))-lam/2*‖z t-Z (t+1)‖^2)) := by
    simp only [map_sub, Finset.sum_sub_distrib] at hs ⊢
    rw [hFu] at hs
    linarith
  simpa only [hZn] using hfirst

private lemma stability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (g : ℕ → E →L[ℝ] ℝ) (z : ℕ → E)
    (lam : ℝ) (T : ℕ) (u : E) (hT : 1 ≤ T) (hu : u ∈ V) (hlam : 0 < lam)
    (hstrong : StrongConvexOn V lam ψ) (hrun : IsOptFTRLRun V ψ g z T) :
    (∑ t ∈ Finset.Icc 1 T, g t (z t-u)) ≤ ψ u-ψ (z 1)+
      (∑ t ∈ Finset.Icc 1 T, ‖g t-g (t-1)‖^2/lam) -
      lam/4*(∑ t ∈ Finset.Icc 2 T, ‖z t-z (t-1)‖^2) := by
  let D : ℕ → ℝ := fun t => ‖z t-(if t<T then z (t+1) else u)‖^2
  have hp : (∑ t ∈ Finset.Icc 2 T, ‖z t-z (t-1)‖^2) ≤ ∑ t ∈ Finset.Icc 1 T, D t := by
    have heq : (∑ t ∈ Finset.Ico 1 T, D t) = ∑ t ∈ Finset.Icc 2 T, ‖z t-z (t-1)‖^2 := by
      refine Finset.sum_bij (fun t _ => t+1) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_Ico] at ht
        simp only [Finset.mem_Icc]
        omega
      · intro a ha b hb h
        omega
      · intro b hb
        refine ⟨b-1, ?_, ?_⟩
        · simp only [Finset.mem_Icc] at hb
          simp only [Finset.mem_Ico]
          omega
        · simp only [Finset.mem_Icc] at hb
          omega
      · intro t ht
        have hlt := (Finset.mem_Ico.mp ht).2
        simp only [D, if_pos hlt, Nat.add_sub_cancel]
        rw [norm_sub_rev]
    rw [← heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      simp only [Finset.mem_Ico] at ht
      simp only [Finset.mem_Icc]
      omega
    · intro t ht hnot
      exact sq_nonneg _
  have h := endpoint V ψ g z lam T u hT hu hstrong hrun
  have hb := Finset.sum_le_sum (s := Finset.Icc 1 T) (fun t ht => show
      (g t-g (t-1)) (z t-(if t<T then z (t+1) else u)) - lam/2*D t ≤
        ‖g t-g (t-1)‖^2/lam - lam/4*D t from by
    have hy := young_bound (g t-g (t-1)) (z t-(if t<T then z (t+1) else u))
      (lam/2) (by positivity)
    rw [show 2*(lam/2)=lam by ring] at hy
    dsimp only [D]
    linarith)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hb
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ lam/4 by positivity)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  dsimp only [D] at hb hp'
  linarith



private lemma convex_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (hc : ConvexOn ℝ X ψ) (x z : E)
    (hx : x ∈ X) (hz : z ∈ X) (g : E →L[ℝ] ℝ) (hd : HasFDerivAt ψ g x) :
    ψ x + g (z - x) ≤ ψ z := by
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x z
  have hline : ConvexOn ℝ (L ⁻¹' X) (ψ ∘ L) := hc.comp_affineMap L
  have hx0 : (0 : ℝ) ∈ L ⁻¹' X := by simpa [L] using hx
  have hz1 : (1 : ℝ) ∈ L ⁻¹' X := by simpa [L] using hz
  have hfd : HasFDerivAt ψ (g) (L 0) := by simpa [L] using hd
  have hld : HasDerivAt (ψ ∘ L) (g (z - x)) 0 := by
    simpa [L] using hfd.comp_hasDerivAt 0 (AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0 : ℝ)))
  have hbound := hline.le_slope_of_hasDerivAt hx0 hz1 (by norm_num) hld
  have hs : g (z - x) ≤ ψ z - ψ x := by
    simpa [slope_def_field, L] using hbound
  linarith


private lemma two_squares {F : Type*} [NormedAddCommGroup F]
    (a b c : F) (A B : ℝ) (ha : ‖a-b‖ ≤ A) (hb : ‖b-c‖ ≤ B) :
    ‖a-c‖^2 ≤ 2*A^2+2*B^2 := by
  have h : ‖a-c‖ ≤ A+B :=
    (norm_sub_le_norm_sub_add_norm_sub a b c).trans (add_le_add ha hb)
  have hs := mul_self_le_mul_self (norm_nonneg (a-c)) h
  nlinarith [sq_nonneg (A-B)]

private lemma energy_split (A : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, A t) = A 1 + ∑ t ∈ Finset.Icc 2 T, A t := by
  have hs : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hs, Finset.sum_insert (by simp)]



theorem solution {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [FiniteDimensional ℝ EY]
    (X : Set EX) (Y : Set EY) (f : EX → EY → ℝ)
    (gx : EX → EY → EX →L[ℝ] ℝ) (gy : EX → EY → EY →L[ℝ] ℝ)
    (ψX : EX → ℝ) (ψY : EY → ℝ) (x : ℕ → EX) (y : ℕ → EY)
    (LXX LXY LYY lamX lamY : ℝ) (T : ℕ)
    (hT : 1 ≤ T) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXclosed : IsClosed X) (hYclosed : IsClosed Y)
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hfx : ∀ v ∈ Y, ConvexOn ℝ X (fun w => f w v))
    (hfy : ∀ u ∈ X, ConcaveOn ℝ Y (f u))
    (hLXX : 0 ≤ LXX) (hLXY : 0 ≤ LXY) (hLYY : 0 ≤ LYY)
    (hlamX : 0 < lamX) (hlamY : 0 < lamY)
    (hψX : StrongConvexOn X lamX ψX) (hψY : StrongConvexOn Y lamY ψY)
    (hsmooth : IsSmoothSaddleOn X Y f gx gy LXX LXY LYY)
    (hrun : IsOptFTRLSaddleRun X Y ψX ψY gx gy x y T) :
    ∀ u ∈ X, ∀ v ∈ Y,
      (∑ t ∈ Finset.Icc 1 T, (f (x t) v - f u (y t))) ≤
      ψX u - ψX (x 1) + ψY v - ψY (y 1) +
      ‖gx (x 1) (y 1)‖ ^ 2 / lamX + ‖gy (x 1) (y 1)‖ ^ 2 / lamY +
      (∑ t ∈ Finset.Icc 2 T,
        ((2 * LXX ^ 2 / lamX + 2 * LXY ^ 2 / lamY - lamX / 4) *
          ‖x t - x (t - 1)‖ ^ 2)) +
      (∑ t ∈ Finset.Icc 2 T,
        ((2 * LYY ^ 2 / lamY + 2 * LXY ^ 2 / lamX - lamY / 4) *
          ‖y t - y (t - 1)‖ ^ 2))  := by
  intro u hu v hv
  let Gx : ℕ → EX →L[ℝ] ℝ := fun t => if t=0 then 0 else gx (x t) (y t)
  let Gy : ℕ → EY →L[ℝ] ℝ := fun t => if t=0 then 0 else -gy (x t) (y t)
  let DX : ℕ → ℝ := fun t => ‖x t-x (t-1)‖^2
  let DY : ℕ → ℝ := fun t => ‖y t-y (t-1)‖^2
  let AX : ℕ → ℝ := fun t => (2*LXX^2*DX t+2*LXY^2*DY t)/lamX
  let AY : ℕ → ℝ := fun t => (2*LYY^2*DY t+2*LXY^2*DX t)/lamY
  have hxmem (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : x t ∈ X := (hrun.1.2 t ht).1
  have hymem (t : ℕ) (ht : t ∈ Finset.Icc 1 T) : y t ∈ Y := (hrun.2.2 t ht).1
  rcases hsmooth with ⟨U, hU, hXY, hder, hxx, hxy, hyx, hyy⟩
  have hlin (t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
      f (x t) v-f u (y t) ≤ Gx t (x t-u)+Gy t (y t-v) := by
    have hxt := hxmem t ht
    have hyt := hymem t ht
    have hd := hder (x t,y t) (hXY ⟨hxt,hyt⟩)
    have hc := convex_support X (fun a => f a (y t)) (hfx (y t) hyt)
      (x t) u hxt hu (gx (x t) (y t)) hd.1
    have hd' := convex_support Y (fun b => -f (x t) b) (hfy (x t) hxt).neg
      (y t) v hyt hv (-gy (x t) (y t)) hd.2.neg
    have ht0 : t ≠ 0 := by have := (Finset.mem_Icc.mp ht).1; omega
    simp only [Gx, Gy, if_neg ht0, ContinuousLinearMap.neg_apply, map_sub] at hc hd' ⊢
    linarith
  have hlinear := Finset.sum_le_sum hlin
  rw [Finset.sum_add_distrib] at hlinear
  have hrx := stability X ψX Gx x lamX T u hT hu hlamX hψX hrun.1
  have hry := stability Y ψY Gy y lamY T v hT hv hlamY hψY hrun.2
  have hgradX (t : ℕ) (ht : t ∈ Finset.Icc 2 T) :
      ‖Gx t-Gx (t-1)‖^2 ≤ 2*LXX^2*DX t+2*LXY^2*DY t := by
    have ht' : t ∈ Finset.Icc 1 T := by have := Finset.mem_Icc.mp ht; simp only [Finset.mem_Icc]; omega
    have htprev : t-1 ∈ Finset.Icc 1 T := by have := Finset.mem_Icc.mp ht; simp only [Finset.mem_Icc]; omega
    have htn : t ≠ 0 := by have := Finset.mem_Icc.mp ht; omega
    have hpn : t-1 ≠ 0 := by have := Finset.mem_Icc.mp ht; omega
    have h := two_squares (gx (x t) (y t)) (gx (x (t-1)) (y t)) (gx (x (t-1)) (y (t-1)))
      (LXX*‖x t-x (t-1)‖) (LXY*‖y t-y (t-1)‖)
      (hxx _ (hxmem t ht') _ (hxmem _ htprev) _ (hymem t ht'))
      (hxy _ (hxmem _ htprev) _ (hymem t ht') _ (hymem _ htprev))
    simp only [Gx, if_neg htn, if_neg hpn, DX, DY]
    nlinarith [h]
  have hgradY (t : ℕ) (ht : t ∈ Finset.Icc 2 T) :
      ‖Gy t-Gy (t-1)‖^2 ≤ 2*LYY^2*DY t+2*LXY^2*DX t := by
    have ht' : t ∈ Finset.Icc 1 T := by have := Finset.mem_Icc.mp ht; simp only [Finset.mem_Icc]; omega
    have htprev : t-1 ∈ Finset.Icc 1 T := by have := Finset.mem_Icc.mp ht; simp only [Finset.mem_Icc]; omega
    have htn : t ≠ 0 := by have := Finset.mem_Icc.mp ht; omega
    have hpn : t-1 ≠ 0 := by have := Finset.mem_Icc.mp ht; omega
    have h := two_squares (gy (x t) (y t)) (gy (x (t-1)) (y t)) (gy (x (t-1)) (y (t-1)))
      (LXY*‖x t-x (t-1)‖) (LYY*‖y t-y (t-1)‖)
      (hyx _ (hxmem t ht') _ (hxmem _ htprev) _ (hymem t ht'))
      (hyy _ (hxmem _ htprev) _ (hymem t ht') _ (hymem _ htprev))
    have he : ‖Gy t-Gy (t-1)‖ = ‖gy (x t) (y t)-gy (x (t-1)) (y (t-1))‖ := by
      simp only [Gy, if_neg htn, if_neg hpn, neg_sub_neg, norm_sub_rev]
    rw [he]
    dsimp only [DX, DY]
    nlinarith [h]
  have hex : (∑ t ∈ Finset.Icc 1 T, ‖Gx t-Gx (t-1)‖^2/lamX) ≤
      ‖gx (x 1) (y 1)‖^2/lamX + ∑ t ∈ Finset.Icc 2 T, AX t := by
    rw [energy_split _ T hT]
    simp only [Nat.sub_self, Gx, if_pos rfl, if_neg (show (1:ℕ) ≠ 0 by omega), sub_zero]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t ht
    exact div_le_div_of_nonneg_right (hgradX t ht) hlamX.le
  have hey : (∑ t ∈ Finset.Icc 1 T, ‖Gy t-Gy (t-1)‖^2/lamY) ≤
      ‖gy (x 1) (y 1)‖^2/lamY + ∑ t ∈ Finset.Icc 2 T, AY t := by
    rw [energy_split _ T hT]
    simp only [Nat.sub_self, Gy, if_pos rfl, if_neg (show (1:ℕ) ≠ 0 by omega), sub_zero, norm_neg]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro t ht
    exact div_le_div_of_nonneg_right (hgradY t ht) hlamY.le
  have halg : (∑ t ∈ Finset.Icc 2 T, AX t)+(∑ t ∈ Finset.Icc 2 T, AY t)-
      lamX/4*(∑ t ∈ Finset.Icc 2 T, DX t)-lamY/4*(∑ t ∈ Finset.Icc 2 T, DY t) =
      (∑ t ∈ Finset.Icc 2 T, (2*LXX^2/lamX+2*LXY^2/lamY-lamX/4)*DX t)+
      (∑ t ∈ Finset.Icc 2 T, (2*LYY^2/lamY+2*LXY^2/lamX-lamY/4)*DY t) := by
    have hp (t : ℕ) : AX t+AY t-lamX/4*DX t-lamY/4*DY t =
        (2*LXX^2/lamX+2*LXY^2/lamY-lamX/4)*DX t+
        (2*LYY^2/lamY+2*LXY^2/lamX-lamY/4)*DY t := by
      dsimp only [AX, AY]
      ring
    have hs := Finset.sum_congr (s₁ := Finset.Icc 2 T) rfl (fun t ht => hp t)
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] using hs
  dsimp only [DX, DY] at halg
  linarith only [hlinear, hrx, hry, hex, hey, halg]

