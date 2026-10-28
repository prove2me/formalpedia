-- Prove2me | solution 1 for OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:05:41.980038+00:00
-- url     : https://prove2.me/submissions/00708f95-71e6-40f9-9f2b-2fd17c153662

import Mathlib
import Definitions.Def_OAIQ3Ho000
import Definitions.Def_OAIQ3Ho001

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MultiplicityComplete

noncomputable section

section PositiveWeightLayer
open Set Filter MeasureTheory Function
open scoped Topology InnerProductSpace
namespace StrictHotSpots.PositiveWeight
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [Nonempty X] [FiniteDimensional ℝ E] in
lemma moment_apply (F : C(X,E)) (f : C(X,ℝ)) : moment μ F f = ∫ s, f s • F s ∂μ := rfl

omit [Nonempty X] in
lemma dual_moment (F : C(X,E)) (f : C(X,ℝ)) (l : E →L[ℝ] ℝ) :
    l (moment μ F f) = ∫ s, f s * l (F s) ∂μ := by
  rw [moment_apply,← l.integral_comp_comm (product_integrable μ F f)]
  congr 1
  funext s
  exact l.map_smul (f s) (F s)

omit [Nonempty X] in
lemma integral_sq_pos [μ.IsOpenPosMeasure] (f : C(X,ℝ)) (hf : ∃ x, f x ≠ 0) :
    0 < ∫ s, (f s)^2 ∂μ := by
  have hn : 0 ≤ ∫ s, (f s)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  by_contra hp
  have hz : (∫ s, (f s)^2 ∂μ) = 0 := le_antisymm (le_of_not_gt hp) hn
  have hi : Integrable (fun s => (f s)^2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have ha := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hz
  have hae : f =ᵐ[μ.restrict univ] (0 : X → ℝ) := by
    rw [Measure.restrict_univ]
    filter_upwards [ha] with x hx
    exact eq_zero_of_pow_eq_zero hx
  have he := Measure.eqOn_open_of_ae_eq hae isOpen_univ f.continuous.continuousOn continuousOn_const
  obtain ⟨x,hx⟩ := hf
  exact hx (he (mem_univ x))

omit [Nonempty X] in
lemma moment_surjective [μ.IsOpenPosMeasure] (F : C(X,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) : Surjective (moment μ F) := by
  let G : E →ₗ[ℝ] E := (moment μ F).toLinearMap.comp (probe F)
  have hz (a : E) (ha : G a = 0) : a = 0 := by
    by_contra hn
    obtain ⟨s,hs⟩ := hF a hn
    have hp := integral_sq_pos μ (probe F a) ⟨s,ne_of_gt hs⟩
    have he := dual_moment μ F (probe F a) (innerSL ℝ a)
    have hv : (∫ s, (probe F a s)^2 ∂μ) = 0 := by
      change inner ℝ a (G a) = ∫ s, inner ℝ a (F s) * inner ℝ a (F s) ∂μ at he
      rw [ha,inner_zero_right] at he
      simpa only [probe,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,pow_two] using he.symm
    linarith
  have hi : Injective G := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hab,sub_self]
  intro a
  obtain ⟨b,hb⟩ := G.surjective_of_injective hi a
  exact ⟨probe F b,hb⟩

omit [CompactSpace X] [Nonempty X] [MeasurableSpace X] [OpensMeasurableSpace X] in
lemma positive_convex : Convex ℝ (positive (X := X)) := by
  intro f hf g hg a b ha hb hab s
  change 0 < a * f s + b * g s
  by_cases hza : a = 0
  · have hbo : b = 1 := by linarith
    simpa [hza,hbo] using hg s
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm hza)) (hf s))
      (mul_nonneg hb (hg s).le)
omit [MeasurableSpace X] [OpensMeasurableSpace X] in
lemma positive_open : IsOpen (positive (X := X)) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set X).Nonempty) f.continuous.continuousOn
  refine ⟨f x,hf x,?_⟩
  intro g hg s
  have hd : |g s-f s| < f x := by
    rw [← Real.dist_eq]
    exact (ContinuousMap.dist_apply_le_dist s).trans_lt hg
  have hm : f x ≤ f s := hx (mem_univ s)
  have hl := (abs_lt.mp hd).1
  linarith




theorem exists_positive_annihilator [μ.IsOpenPosMeasure] (F : C(X,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) :
    ∃ w : C(X,ℝ), (∀ s, 0 < w s) ∧ (∫ s, w s • F s ∂μ) = 0 := by
  let T := moment μ F
  have hT : Surjective T := moment_surjective μ F hF
  have ho : IsOpen (T '' positive) := T.isOpenMap hT _ positive_open
  have hc : Convex ℝ (T '' positive) := positive_convex.linear_image T.toLinearMap
  have hz : (0:E) ∈ T '' positive := by
    by_contra hn
    obtain ⟨l,hl⟩ := geometric_hahn_banach_open_point hc ho hn
    let one : C(X,ℝ) := ContinuousMap.const X 1
    have hone : one ∈ positive := fun _ => zero_lt_one
    have hnegative (f : C(X,ℝ)) (hf : f ∈ positive) : l (T f) < 0 := by
      simpa only [map_zero] using hl (T f) ⟨f,hf,rfl⟩
    have hl0 : l ≠ 0 := by
      intro he
      have h := hnegative one hone
      rw [he] at h
      exact (lt_irrefl (0:ℝ)) h
    let a : E := (InnerProductSpace.toDual ℝ E).symm l
    have ha : a ≠ 0 := by
      intro hz
      have he := congrArg (InnerProductSpace.toDual ℝ E) hz
      simp only [a,LinearIsometryEquiv.apply_symm_apply,map_zero] at he
      exact hl0 he
    obtain ⟨s,hs⟩ := hF a ha
    have hla : ∀ x, l (F x) = inner ℝ a (F x) := by
      intro x
      exact congrArg (fun k : E →L[ℝ] ℝ => k (F x))
        ((InnerProductSpace.toDual ℝ E).apply_symm_apply l).symm
    let q : C(X,ℝ) := ⟨fun x => max (l (F x)) 0,(l.continuous.comp F.continuous).max continuous_const⟩
    have hqnonneg (x : X) : 0 ≤ q x := le_max_right _ _
    have hqpos : 0 < q s := lt_of_lt_of_le (by rwa [hla s]) (le_max_left _ _)
    let A := ∫ x, (q x)^2 ∂μ
    have hA : 0 < A := integral_sq_pos μ q ⟨s,ne_of_gt hqpos⟩
    have he : l (T q) = A := by
      rw [show T q = moment μ F q from rfl,dual_moment]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change max (l (F x)) 0 * l (F x) = (max (l (F x)) 0)^2
        by_cases h : 0 ≤ l (F x)
        · rw [max_eq_left h,pow_two]
        · rw [max_eq_right (le_of_not_ge h),zero_mul,zero_pow (by decide : 2 ≠ 0)]
    let B := l (T one)
    let c := (|B|+1)/A
    have hcpos : 0 < c := div_pos (by positivity) hA
    let f := one + c • q
    have hf : f ∈ positive := by
      intro x
      change 0 < 1 + c * q x
      linarith [mul_nonneg hcpos.le (hqnonneg x)]
    have hbad := hnegative f hf
    have hval : l (T f) = B + (|B|+1) := by
      simp only [f,map_add,map_smul,smul_eq_mul,he]
      change B + c*A = B+(|B|+1)
      dsimp only [c]
      rw [div_mul_cancel₀ _ hA.ne']
    rw [hval] at hbad
    linarith [neg_abs_le B]
  obtain ⟨w,hw,he⟩ := hz
  exact ⟨w,hw,he⟩
end StrictHotSpots.PositiveWeight
end PositiveWeightLayer

section CirclePositiveWeightLayer
open Set MeasureTheory
open scoped Topology InnerProductSpace
namespace StrictHotSpots.PositiveWeight
local instance instFactLtRealOfNatHMulPi_solutions : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


theorem exists_circle_weight (F : C(Circle,E))
    (hF : ∀ a : E, a ≠ 0 → ∃ s, 0 < inner ℝ a (F s)) :
    ∃ w : ℝ → ℝ, Continuous w ∧ Function.Periodic w (2*Real.pi) ∧
      (∀ θ, 0 < w θ) ∧ ∀ a : E,
        (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ))) = 0 := by
  let G : C(AddCircle (2*Real.pi),E) := F.comp ⟨AddCircle.homeomorphCircle',AddCircle.homeomorphCircle'.continuous⟩
  have hG (a : E) (ha : a ≠ 0) : ∃ s, 0 < inner ℝ a (G s) := by
    obtain ⟨s,hs⟩ := hF a ha
    refine ⟨AddCircle.homeomorphCircle'.symm s,?_⟩
    change 0 < inner ℝ a (F (AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm s)))
    rwa [Homeomorph.apply_symm_apply]
  obtain ⟨w,hw,he⟩ := exists_positive_annihilator (volume : Measure (AddCircle (2*Real.pi))) G hG
  let W : ℝ → ℝ := fun θ => w (θ : AddCircle (2*Real.pi))
  refine ⟨W,w.continuous.comp (AddCircle.continuous_mk' (2*Real.pi)),?_,fun θ => hw _,?_⟩
  · intro θ
    exact congrArg w (AddCircle.coe_add_period (2*Real.pi) θ)
  · intro a
    have hh := dual_moment (volume : Measure (AddCircle (2*Real.pi))) G w (innerSL ℝ a)
    rw [moment_apply,he,map_zero] at hh
    have hI := AddCircle.intervalIntegral_preimage (2*Real.pi) 0
      (fun s : AddCircle (2*Real.pi) => w s*inner ℝ a (G s))
    simp only [zero_add] at hI
    simpa only [W,G,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
      AddCircle.homeomorphCircle'_apply_mk] using hI.trans hh.symm
end StrictHotSpots.PositiveWeight
end CirclePositiveWeightLayer

section PlanarCrossingLayer


open Set Filter _root_.Complex Metric
open scoped unitInterval Topology ComplexConjugate
namespace StrictHotSpots.PlanarTopology

private lemma boundary_halfPlane {x b : ℂ} (hx : ‖x‖ ≤ 1) (hb : ‖b‖ = 1)
    (hne : x ≠ b) : 0 < ((x-b)*(-conj b)).re := by
  have hx' : normSq x ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  have hb' : normSq b = 1 := by rw [normSq_eq_norm_sq,hb]; norm_num
  have hd : 0 < normSq (x-b) := normSq_pos.mpr (sub_ne_zero.mpr hne)
  simp only [normSq_apply,sub_re,sub_im] at hx' hb' hd
  simp only [mul_re,sub_re,sub_im,neg_re,neg_im,conj_re,conj_im]
  nlinarith

private lemma log_difference {P : C(unitInterval,ℂ)} {b : ℂ}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hb : ‖b‖ = 1) (hne : ∀ s, P s ≠ b)
    {l : C(unitInterval,ℂ)} (hl : ∀ s, exp (l s) = P s-b) :
    l 1-l 0 = log ((P 1-b)*(-conj b))-log ((P 0-b)*(-conj b)) := by
  let w : unitInterval → ℂ := fun s => (P s-b)*(-conj b)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hwpos (s) : 0 < (w s).re := boundary_halfPlane (hP s) hb (hne s)
  have hws (s) : w s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (hwpos s))
  have hwn (s) : w s ≠ 0 := fun h => by simpa [h] using hwpos s
  have hc : Continuous (fun s => log (w s)-log (w 0)+l 0) :=
    ((hw.clog hws).sub continuous_const).add continuous_const
  have he (s) : exp (log (w s)-log (w 0)+l 0) = exp (l s) := by
    rw [exp_add,exp_sub,exp_log (hwn s),exp_log (hwn 0),hl s,hl 0]
    dsimp [w]
    have hb0 : -conj b ≠ 0 := neg_ne_zero.mpr ((map_ne_zero (starRingEnd ℂ)).mpr (by intro h; simp [h] at hb))
    field_simp [sub_ne_zero.mpr (hne 0),neg_ne_zero.mp hb0]
  have eqfun : (fun s => log (w s)-log (w 0)+l 0) = l := by
    exact isCoveringMap_exp.eq_of_comp_eq hc l.continuous
      (funext fun s => Subtype.ext (he s)) 0 (by simp)
  have heq := congrFun eqfun 1
  dsimp [w] at heq
  linear_combination -heq

private lemma square_log {P N : C(unitInterval,ℂ)} (hne : ∀ s t, P s ≠ N t) :
    ∃ L : C(unitInterval × unitInterval,ℂ), ∀ s t, exp (L (s,t)) = P s-N t := by
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : LocallyPathConnectedSpace unitInterval := (convex_Icc (0:ℝ) 1).locallyPathConnectedSpace
  let f : C(unitInterval × unitInterval,{z : ℂ // z ≠ 0}) :=
    ⟨fun st => ⟨P st.1-N st.2,sub_ne_zero.mpr (hne st.1 st.2)⟩,
      ((P.continuous.comp continuous_fst).sub (N.continuous.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨L,hL,-⟩ := isCoveringMap_exp.existsUnique_continuousMap_lifts f (0,0)
    (log (f (0,0))) (Subtype.ext (exp_log (f (0,0)).property))
  exact ⟨L,fun s t => congrArg Subtype.val (congrFun hL.2 (s,t))⟩



private lemma arg_product_rightHalfPlane {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    arg (u*conj v) = arg u-arg v := by
  have h₁ := neg_pi_div_two_lt_arg_iff.mpr (Or.inl hu)
  have h₂ := arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have h₃ := neg_pi_div_two_lt_arg_iff.mpr (Or.inl hv)
  have h₄ := arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hvπ : arg v ≠ Real.pi := by linarith [Real.pi_pos]
  have hc : arg (conj v) = -arg v := by rw [arg_conj,ite_eq_right hvπ]
  rw [arg_mul (by intro h; simp [h] at hu)
    (by intro h; have := congrArg re h; simp only [conj_re,zero_re] at this; linarith)
    (by rw [hc]; constructor <;> linarith),hc,sub_eq_add_neg]

private lemma log_difference_im {P : C(unitInterval,ℂ)} {b : ℂ}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hb : ‖b‖ = 1) (hne : ∀ s, P s ≠ b)
    {l : C(unitInterval,ℂ)} (hl : ∀ s, exp (l s) = P s-b) :
    (l 1-l 0).im = arg ((P 1-b)*conj (P 0-b)) := by
  rw [log_difference hP hb hne hl,sub_im,log_im,log_im,
    ← arg_product_rightHalfPlane (boundary_halfPlane (hP 1) hb (hne 1))
      (boundary_halfPlane (hP 0) hb (hne 0))]
  congr 1
  have hbc : (-conj b)*conj (-conj b) = 1 := by
    rw [mul_conj,normSq_eq_norm_sq,norm_neg,norm_conj,hb]
    norm_num
  rw [map_mul]
  calc
    (P 1-b)*(-conj b)*(conj (P 0-b)*conj (-conj b)) =
        ((P 1-b)*conj (P 0-b))*((-conj b)*conj (-conj b)) := by ring
    _ = _ := by rw [hbc,mul_one]

private lemma no_positive_chord_ratio {a c z : ℂ} {k : ℝ}
    (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) (hz : ‖z‖ ≤ 1) (hac : a ≠ c) (haz : a ≠ z)
    (hk : 0 < k) (he : c-z = (k : ℂ)*(a-z)) : False := by
  have hna : normSq a = 1 := by rw [normSq_eq_norm_sq,ha]; norm_num
  have hnc : normSq c = 1 := by rw [normSq_eq_norm_sq,hc]; norm_num
  have hnz : normSq z ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hnaz : 0 < normSq (a-z) := normSq_pos.mpr (sub_ne_zero.mpr haz)
  have hce : c = z+(k : ℂ)*(a-z) := by linear_combination he
  have hid : normSq c-normSq a =
      (k-1)*(normSq a-normSq z+k*normSq (a-z)) := by
    rw [hce]
    simp only [normSq_apply,add_re,add_im,mul_re,mul_im,sub_re,sub_im,ofReal_re,ofReal_im]
    ring
  rw [hna,hnc,sub_self] at hid
  have hp : 0 < 1-normSq z+k*normSq (a-z) :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr hnz) (mul_pos hk hnaz)
  have he1 : k = 1 := by
    have hh := (mul_eq_zero.mp hid.symm).resolve_right hp.ne'
    linarith
  rw [he1,ofReal_one,one_mul] at he
  exact hac (sub_left_injective he).symm




theorem disk_paths_cross_chord {P N : C(unitInterval,ℂ)}
    (hP : ∀ s, ‖P s‖ ≤ 1) (hN : ∀ t, ‖N t‖ ≤ 1)
    (hP0 : ‖P 0‖ = 1) (hP1 : ‖P 1‖ = 1) (hneP : P 0 ≠ P 1)
    (hN0 : ‖N 0‖ = 1) (hN1 : ‖N 1‖ = 1)
    (hup : 0 < ((P 1-N 0)*conj (P 0-N 0)).im)
    (hdn : ((P 1-N 1)*conj (P 0-N 1)).im < 0) :
    ∃ s t, P s = N t := by
  by_contra h
  push Not at h
  obtain ⟨L,hL⟩ := square_log h
  let D : unitInterval → ℂ := fun t => L (1,t)-L (0,t)
  have hD : Continuous D := by dsimp [D]; fun_prop
  have hed (t : unitInterval) (ht : ‖N t‖ = 1) :
      (D t).im = arg ((P 1-N t)*conj (P 0-N t)) :=
    log_difference_im hP ht (fun s => h s t)
      (l := ⟨fun s => L (s,t),by fun_prop⟩) (fun s => hL s t)
  have hp : 0 < (D 0).im := by
    rw [hed 0 hN0]
    have hge := arg_nonneg_iff.mpr hup.le
    have hn : arg ((P 1-N 0)*conj (P 0-N 0)) ≠ 0 := by
      intro ht
      exact hup.ne' (arg_eq_zero_iff.mp ht).2
    exact hge.lt_of_ne' hn
  have hn : (D 1).im < 0 := by rw [hed 1 hN1]; exact arg_neg_iff.mpr hdn
  obtain ⟨t,ht⟩ := intermediate_value_univ (1 : unitInterval) 0 (continuous_im.comp hD) ⟨hn.le,hp.le⟩
  have he : (P 1-N t) = exp (D t)*(P 0-N t) := by
    have hd : exp (D t) = (P 1-N t)/(P 0-N t) := by dsimp only [D]; rw [exp_sub,hL,hL]
    exact (div_eq_iff (sub_ne_zero.mpr (h 0 t))).mp hd.symm
  have hex : exp (D t) = (Real.exp (D t).re : ℂ) := by
    apply Complex.ext <;> simp [exp_re,exp_im,show (D t).im = 0 from ht]
  rw [hex] at he
  exact no_positive_chord_ratio hP0 hP1 (hN t) hneP (h 0 t) (Real.exp_pos _) he

end StrictHotSpots.PlanarTopology
end PlanarCrossingLayer

section DiskSignTopologyLayer

open Set Filter Metric _root_.Complex
open scoped unitInterval Topology ComplexConjugate
namespace StrictHotSpots.PlanarTopology

private lemma disk_positive_open {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1)) : IsOpen (ball (0 : ℂ) 1 ∩ {z | 0 < u z}) := by
  exact (hu.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_Ioi



lemma join_positive_interior {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1)) {a : ℂ}
    (ha : a ∈ closedBall (0 : ℂ) 1) (hua : 0 < u a) :
    ∃ a' ∈ ball (0 : ℂ) 1 ∩ {z | 0 < u z},
      JoinedIn (closedBall (0 : ℂ) 1 ∩ {z | 0 < u z}) a a' := by
  obtain ⟨ε,hε,hεu⟩ := (Metric.continuousWithinAt_iff.mp (hu a ha)) (u a) hua
  have hpos : closedBall (0 : ℂ) 1 ∩ ball a ε ⊆ {z | 0 < u z} := by
    intro z hz
    have hd := hεu hz.1 hz.2
    rw [Real.dist_eq] at hd
    have := (abs_lt.mp hd).1
    change 0 < u z
    linarith
  have hacl : a ∈ closure (ball (0 : ℂ) 1) := by rwa [closure_ball (0 : ℂ) one_ne_zero]
  obtain ⟨a',ha',hda'⟩ := Metric.mem_closure_iff.mp hacl ε hε
  have hsa : a ∈ closedBall (0 : ℂ) 1 ∩ ball a ε := ⟨ha,mem_ball_self hε⟩
  have hsa' : a' ∈ closedBall (0 : ℂ) 1 ∩ ball a ε :=
    ⟨ball_subset_closedBall ha',by simpa only [mem_ball,dist_comm] using hda'⟩
  refine ⟨a',⟨ha',hpos hsa'⟩,?_⟩
  exact (((convex_closedBall (0 : ℂ) 1).inter (convex_ball a ε)).isPathConnected
    ⟨a,hsa⟩ |>.joinedIn a hsa a' hsa').mono (fun z hz => ⟨hz.1,hpos hz⟩)

lemma join_positive_closedDisk {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hc : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    {a c : ℂ} (ha : a ∈ closedBall (0 : ℂ) 1) (hc' : c ∈ closedBall (0 : ℂ) 1)
    (hua : 0 < u a) (huc : 0 < u c) :
    JoinedIn (closedBall (0 : ℂ) 1 ∩ {z | 0 < u z}) a c := by
  obtain ⟨a',ha',hja⟩ := join_positive_interior hu ha hua
  obtain ⟨c',hc'',hjc⟩ := join_positive_interior hu hc' huc
  have hpath := (disk_positive_open hu).isConnected_iff_isPathConnected.mp hc
  have hj := (hpath.joinedIn a' ha' c' hc'').mono
    (show ball (0 : ℂ) 1 ∩ {z | 0 < u z} ⊆ closedBall (0 : ℂ) 1 ∩ {z | 0 < u z} from
      fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩)
  exact (hja.trans hj).trans hjc.symm



theorem no_alternating_boundary_signs {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hp : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hn : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {a b c d : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hac : a ≠ c) (hup : 0 < ((c-b)*conj (a-b)).im)
    (hdn : ((c-d)*conj (a-d)).im < 0)
    (hua : 0 < u a) (hub : u b < 0) (huc : 0 < u c) (hud : u d < 0) : False := by
  have hacl : a ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,ha,le_refl]
  have hccl : c ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hc,le_refl]
  have hbcl : b ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hb,le_refl]
  have hdcl : d ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall,dist_zero_right,hd,le_refl]
  have hP := join_positive_closedDisk hu hp hacl hccl hua huc
  have hneg : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < -u z}) := by
    simpa only [neg_pos] using hn
  have hN := join_positive_closedDisk hu.neg hneg hbcl hdcl (neg_pos.mpr hub) (neg_pos.mpr hud)
  let P : C(unitInterval,ℂ) := hP.somePath.toContinuousMap
  let N : C(unitInterval,ℂ) := hN.somePath.toContinuousMap
  have hPs (s) : ‖P s‖ ≤ 1 := by
    have hh := (hP.somePath_mem s).1
    simpa only [P,N,Path.coe_toContinuousMap,mem_closedBall,dist_zero_right] using hh
  have hNs (s) : ‖N s‖ ≤ 1 := by
    have hh := (hN.somePath_mem s).1
    simpa only [P,N,Path.coe_toContinuousMap,mem_closedBall,dist_zero_right] using hh
  have hP0 : P 0 = a := hP.somePath.source
  have hP1 : P 1 = c := hP.somePath.target
  have hN0 : N 0 = b := hN.somePath.source
  have hN1 : N 1 = d := hN.somePath.target
  obtain ⟨s,t,hst⟩ := disk_paths_cross_chord hPs hNs (hP0.symm ▸ ha) (hP1.symm ▸ hc)
    (by simpa only [hP0,hP1] using hac) (hN0.symm ▸ hb) (hN1.symm ▸ hd)
    (by simpa only [hP0,hP1,hN0] using hup) (by simpa only [hP0,hP1,hN1] using hdn)
  have hpos : 0 < u (P s) := (hP.somePath_mem s).2
  have hneg : 0 < -u (N t) := (hN.somePath_mem t).2
  rw [hst] at hpos
  linarith

end StrictHotSpots.PlanarTopology
end DiskSignTopologyLayer

section CircleSignMomentsLayer



open Set MeasureTheory
namespace StrictHotSpots.CircleSigns

lemma separating_cosine (a b x : ℝ) :
    Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) =
      2*Real.sin ((x-a)/2)*Real.sin ((b-x)/2) := by
  rw [Real.cos_sub_cos]
  have h₁ : ((x-(a+b)/2)+(b-a)/2)/2 = (x-a)/2 := by ring
  have h₂ : ((x-(a+b)/2)-(b-a)/2)/2 = -((b-x)/2) := by ring
  rw [h₁,h₂,Real.sin_neg]
  ring

lemma separating_cosine_pos {α a b x : ℝ} (ha : α < a) (hb : b < α+2*Real.pi)
    (hx : x ∈ Ioo a b) :
    0 < Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) := by
  rw [separating_cosine]
  have h₁ : 0 < Real.sin ((x-a)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
  have h₂ : 0 < Real.sin ((b-x)/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.2]) (by linarith [hx.1])
  positivity

lemma separating_cosine_nonpos {α a b x : ℝ} (ha : α < a) (hab : a < b)
    (hb : b < α+2*Real.pi) (hx : x ∈ Icc α (α+2*Real.pi))
    (hout : x ≤ a ∨ b ≤ x) :
    Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2) ≤ 0 := by
  rw [separating_cosine]
  rcases hout with h | h
  · have h₁ : Real.sin ((x-a)/2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hx.1])
    have h₂ : 0 ≤ Real.sin ((b-x)/2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.1])
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) h₁) h₂
  · have h₁ : 0 ≤ Real.sin ((x-a)/2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hx.2])
    have h₂ : Real.sin ((b-x)/2) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hx.2])
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) h₁) h₂

lemma positive_points_sandwich {h : ℝ → ℝ} (hc : Continuous h) {α x : ℝ}
    (hα : h α < 0) (hβ : h (α+2*Real.pi) < 0)
    (hx : x ∈ Icc α (α+2*Real.pi)) (hh : 0 < h x) :
    ∃ y z, y ∈ Icc α (α+2*Real.pi) ∧ z ∈ Icc α (α+2*Real.pi) ∧
      0 < h y ∧ 0 < h z ∧ y < x ∧ x < z := by
  have hαx : α < x := lt_of_le_of_ne hx.1 (by rintro rfl; linarith)
  have hxβ : x < α+2*Real.pi := lt_of_le_of_ne hx.2 (by intro he; rw [he] at hh; linarith)
  have ho : IsOpen (Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0) :=
    isOpen_Ioo.inter (isOpen_Ioi.preimage hc)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho x ⟨⟨hαx,hxβ⟩,hh⟩
  have hy : x-ε/2 ∈ Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0 := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have : x-ε/2-x = -(ε/2) := by ring
    rw [this,abs_neg,abs_of_pos (by positivity)]
    linarith
  have hz : x+ε/2 ∈ Ioo α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0 := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq]
    have : x+ε/2-x = ε/2 := by ring
    rw [this,abs_of_pos (by positivity)]
    linarith
  exact ⟨_,_,⟨hy.1.1.le,hy.1.2.le⟩,⟨hz.1.1.le,hz.1.2.le⟩,hy.2,hz.2,by linarith,by linarith⟩



theorem moment_sign_changes {h w : ℝ → ℝ} (hc : Continuous h) (wc : Continuous w) (α : ℝ)
    (wp : ∀ x ∈ Icc α (α+2*Real.pi), 0 < w x)
    (hα : h α < 0) (hβ : h (α+2*Real.pi) < 0)
    (hp : ∃ x ∈ Icc α (α+2*Real.pi), 0 < h x)
    (h0 : (∫ x in α..α+2*Real.pi, w x*h x) = 0)
    (hcos : (∫ x in α..α+2*Real.pi, w x*h x*Real.cos x) = 0)
    (hsin : (∫ x in α..α+2*Real.pi, w x*h x*Real.sin x) = 0) :
    ∃ x y z, x ∈ Ioo α (α+2*Real.pi) ∧ z ∈ Ioo α (α+2*Real.pi) ∧
      x < y ∧ y < z ∧ 0 < h x ∧ h y < 0 ∧ 0 < h z := by
  by_contra! hn
  let P : Set ℝ := Icc α (α+2*Real.pi) ∩ h ⁻¹' Ioi 0
  have hP : P.Nonempty := hp
  have hb : BddBelow P := ⟨α,fun x hx => hx.1.1⟩
  have ht : BddAbove P := ⟨α+2*Real.pi,fun x hx => hx.1.2⟩
  let a := sInf P
  let b := sSup P
  have hcl : closure P ⊆ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := by
    apply closure_minimal
    · intro x hx
      refine ⟨hx.1,?_⟩
      change 0 ≤ h x
      exact le_of_lt hx.2
    · exact isClosed_Icc.inter (isClosed_Ici.preimage hc)
  have ham : a ∈ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := hcl (csInf_mem_closure hP hb)
  have hbm : b ∈ Icc α (α+2*Real.pi) ∩ h ⁻¹' Ici 0 := hcl (csSup_mem_closure hP ht)
  have ha : α < a := lt_of_le_of_ne ham.1.1 (by intro he; rw [← he] at ham; exact (not_lt_of_ge ham.2) hα)
  have hβb : b < α+2*Real.pi := lt_of_le_of_ne hbm.1.2 (by intro he; rw [he] at hbm; exact (not_lt_of_ge hbm.2) hβ)
  have hstrict (x : ℝ) (hx : x ∈ P) : a < x ∧ x < b := by
    obtain ⟨y,z,hy,hz,hpy,hpz,hyx,hxz⟩ := positive_points_sandwich hc hα hβ hx.1 hx.2
    exact ⟨lt_of_le_of_lt (csInf_le hb ⟨hy,hpy⟩) hyx,
      lt_of_lt_of_le hxz (le_csSup ht ⟨hz,hpz⟩)⟩
  let p := hP.some
  have hp : p ∈ P := hP.some_mem
  have hsp := hstrict p hp
  have hab : a < b := hsp.1.trans hsp.2
  have hmid (x : ℝ) (hx : x ∈ Ioo a b) : 0 ≤ h x := by
    by_contra! hh
    obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hP hx.1
    obtain ⟨z,hz,hxz⟩ := exists_lt_of_lt_csSup hP hx.2
    have hsy := hstrict y hy
    have hsz := hstrict z hz
    exact (not_lt_of_ge (hn y x z ⟨ha.trans hsy.1,hsy.2.trans hβb⟩
      ⟨ha.trans hsz.1,hsz.2.trans hβb⟩ hyx hxz hy.2 hh)) hz.2
  have hout (x : ℝ) (hx : x ∈ Icc α (α+2*Real.pi)) (hh : x ≤ a ∨ b ≤ x) : h x ≤ 0 := by
    by_contra! hp
    have hs := hstrict x ⟨hx,hp⟩
    rcases hh with h | h <;> linarith [hs.1,hs.2]
  let F : ℝ → ℝ := fun x => Real.cos (x-(a+b)/2)-Real.cos ((b-a)/2)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hnon (x : ℝ) (hx : x ∈ Icc α (α+2*Real.pi)) : 0 ≤ w x*h x*F x := by
    by_cases hi : x ∈ Ioo a b
    · exact mul_nonneg (mul_nonneg (wp x hx).le (hmid x hi)) (separating_cosine_pos ha hβb hi).le
    · have he : x ≤ a ∨ b ≤ x := by simpa only [mem_Ioo,not_and_or,not_lt] using hi
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (wp x hx).le (hout x hx he))
        (separating_cosine_nonpos ha hab hβb hx he)
  have hpos : 0 < ∫ x in α..α+2*Real.pi, w x*h x*F x := by
    apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) ((wc.mul hc).mul hF).continuousOn
    · intro x hx
      exact hnon x ⟨hx.1.le,hx.2⟩
    · exact ⟨p,hp.1,mul_pos (mul_pos (wp p hp.1) hp.2) (separating_cosine_pos ha hβb hsp)⟩
  have heq (x : ℝ) : w x*h x*F x =
      Real.cos ((a+b)/2)*(w x*h x*Real.cos x) +
      Real.sin ((a+b)/2)*(w x*h x*Real.sin x) - Real.cos ((b-a)/2)*(w x*h x) := by
    dsimp [F]
    rw [Real.cos_sub]
    ring
  have he : (∫ x in α..α+2*Real.pi, w x*h x*F x) = 0 := by
    simp_rw [heq]
    rw [intervalIntegral.integral_sub,intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,hcos,hsin,h0]
    · ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  linarith

end StrictHotSpots.CircleSigns
end CircleSignMomentsLayer

section ChordAnglesLayer
open _root_.Complex Set Metric
open scoped ComplexConjugate
namespace StrictHotSpots.PlanarTopology

lemma sine_triple_identity (a b c : ℝ) :
    Real.sin (c-a) - Real.sin (c-b) + Real.sin (a-b) =
      4*Real.sin ((c-b)/2)*Real.sin ((a-b)/2)*Real.sin ((c-a)/2) := by
  have h₂ : Real.sin (c-a) = 2*Real.sin ((c-a)/2)*Real.cos ((c-a)/2) := by
    simpa only [show 2*((c-a)/2) = c-a by ring] using Real.sin_two_mul ((c-a)/2)
  have h₃ := Real.sin_sub_sin (c-b) (a-b)
  have he : ((c-b)-(a-b))/2 = (c-a)/2 := by ring
  rw [he] at h₃
  have h₄ := Real.cos_sub_cos ((c-a)/2) (((c-b)+(a-b))/2)
  have he₁ : ((c-a)/2 + ((c-b)+(a-b))/2)/2 = (c-b)/2 := by ring
  have he₂ : ((c-a)/2 - ((c-b)+(a-b))/2)/2 = -((a-b)/2) := by ring
  rw [he₁,he₂,Real.sin_neg] at h₄
  calc
    _ = 2*Real.sin ((c-a)/2)*(Real.cos ((c-a)/2)-Real.cos (((c-b)+(a-b))/2)) := by
      linarith [h₃]
    _ = _ := by rw [h₄]; ring

lemma chord_exp_det (a b c : ℝ) :
    (((Circle.exp c : ℂ)-(Circle.exp b : ℂ))*
      conj ((Circle.exp a : ℂ)-(Circle.exp b : ℂ))).im =
      4*Real.sin ((c-b)/2)*Real.sin ((a-b)/2)*Real.sin ((c-a)/2) := by
  rw [← sine_triple_identity]
  simp only [Circle.coe_exp,exp_ofReal_mul_I_re,exp_ofReal_mul_I_im,
    mul_im,sub_re,sub_im,conj_re,conj_im,Real.sin_sub]
  ring

lemma angles_no_alternation {u : ℂ → ℝ}
    (hu : ContinuousOn u (closedBall 0 1))
    (hp : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hn : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {α x y z : ℝ} (hαx : α < x) (hxy : x < y) (hyz : y < z) (hzβ : z < α+2*Real.pi)
    (hα : u (Circle.exp α) < 0) (hx : 0 < u (Circle.exp x))
    (hy : u (Circle.exp y) < 0) (hz : 0 < u (Circle.exp z)) : False := by
  have hzx : (Circle.exp z : ℂ) ≠ (Circle.exp x : ℂ) := by
    intro he
    have hc : Circle.exp z = Circle.exp x := Subtype.ext he
    have := Circle.exp_injOn_Ico (a := α) (b := α+2*Real.pi) (by linarith)
      ⟨by linarith,hzβ⟩ ⟨hαx.le,by linarith⟩ hc
    linarith
  have hup : 0 < (((Circle.exp x : ℂ)-(Circle.exp y : ℂ))*
      conj ((Circle.exp z : ℂ)-(Circle.exp y : ℂ))).im := by
    rw [chord_exp_det]
    have hs₁ : Real.sin ((x-y)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    have hs₂ : 0 < Real.sin ((z-y)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₃ : Real.sin ((x-z)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hs₁) hs₂) hs₃
  have hdn : (((Circle.exp x : ℂ)-(Circle.exp α : ℂ))*
      conj ((Circle.exp z : ℂ)-(Circle.exp α : ℂ))).im < 0 := by
    rw [chord_exp_det]
    have hs₁ : 0 < Real.sin ((x-α)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₂ : 0 < Real.sin ((z-α)/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs₃ : Real.sin ((x-z)/2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) hs₁) hs₂) hs₃
  exact no_alternating_boundary_signs hu hp hn (Circle.exp z).norm_coe (Circle.exp y).norm_coe
    (Circle.exp x).norm_coe (Circle.exp α).norm_coe hzx hup hdn hz hy hx hα

end StrictHotSpots.PlanarTopology
end ChordAnglesLayer

section DiskBoundaryMomentsLayer
open Set MeasureTheory Metric
namespace StrictHotSpots.CircleSigns

lemma periodic_weighted_signs {h w : ℝ → ℝ} (hc : Continuous h) (wc : Continuous w)
    (hp : Function.Periodic h (2*Real.pi)) (wp : Function.Periodic w (2*Real.pi))
    (hw : ∀ x, 0 < w x) (hne : ∃ x, h x ≠ 0)
    (hi : (∫ x in (0:ℝ)..2*Real.pi, w x*h x) = 0) :
    (∃ x, h x < 0) ∧ (∃ x, 0 < h x) := by
  have hneg {f : ℝ → ℝ} (fc : Continuous f) (fp : Function.Periodic f (2*Real.pi))
      (fn : ∃ x, f x ≠ 0) (fi : (∫ x in (0:ℝ)..2*Real.pi, w x*f x) = 0) : ∃ x, f x < 0 := by
    by_contra! hh
    obtain ⟨x,hx⟩ := fn
    have hxx : 0 < f x := lt_of_le_of_ne (hh x) hx.symm
    have hi' : 0 < ∫ y in x..x+2*Real.pi, w y*f y := by
      apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) (wc.mul fc).continuousOn
      · intro y _
        exact mul_nonneg (hw y).le (hh y)
      · exact ⟨x,⟨le_rfl,by linarith [Real.pi_pos]⟩,mul_pos (hw x) hxx⟩
    have he := (wp.mul fp).intervalIntegral_add_eq x 0
    simp only [zero_add,Pi.mul_apply] at he
    rw [fi] at he
    linarith
  constructor
  · exact hneg hc hp hne hi
  · obtain ⟨x,hx⟩ := hneg hc.neg (fun x => by simp only [Pi.neg_apply,hp x]) (by simpa using hne) (by
      simpa only [Pi.neg_apply,mul_neg,intervalIntegral.integral_neg,neg_zero] using congrArg Neg.neg hi)
    exact ⟨x,neg_lt_zero.mp hx⟩

lemma circle_trace_continuous {u : ℂ → ℝ} (hu : ContinuousOn u (closedBall 0 1)) :
    Continuous (fun θ : ℝ => u (Circle.exp θ : ℂ)) := by
  apply hu.comp_continuous
  · fun_prop
  · intro θ
    simp only [mem_closedBall,dist_zero_right,(Circle.exp θ).norm_coe,le_refl]



theorem disk_moments_nonzero {u : ℂ → ℝ} (hu : ContinuousOn u (closedBall 0 1))
    (hpos : IsConnected (ball (0 : ℂ) 1 ∩ {z | 0 < u z}))
    (hneg : IsConnected (ball (0 : ℂ) 1 ∩ {z | u z < 0}))
    {w : ℝ → ℝ} (wc : Continuous w) (wp : Function.Periodic w (2*Real.pi))
    (hw : ∀ θ, 0 < w θ) (hne : ∃ θ, u (Circle.exp θ : ℂ) ≠ 0)
    (hi : (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)) = 0) :
    (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)*Real.cos θ) ≠ 0 ∨
      (∫ θ in (0:ℝ)..2*Real.pi, w θ*u (Circle.exp θ : ℂ)*Real.sin θ) ≠ 0 := by
  by_contra! hm
  let h : ℝ → ℝ := fun θ => u (Circle.exp θ : ℂ)
  have hc : Continuous h := circle_trace_continuous hu
  have hp : Function.Periodic h (2*Real.pi) := by
    intro θ
    exact congrArg (fun z : Circle => u (z : ℂ)) (Circle.exp_add_two_pi θ)
  obtain ⟨⟨α,hα⟩,⟨p,hp'⟩⟩ := periodic_weighted_signs hc wc hp wp hw hne hi
  have hα' : h (α+2*Real.pi) < 0 := by rw [hp]; exact hα
  have hposI : ∃ x ∈ Icc α (α+2*Real.pi), 0 < h x := by
    have hr := hp.image_Icc Real.two_pi_pos α
    have hx : h p ∈ Set.range h := ⟨p,rfl⟩
    rw [← hr] at hx
    obtain ⟨x,hx,hex⟩ := hx
    exact ⟨x,hx,hex ▸ hp'⟩
  have hi' : (∫ x in α..α+2*Real.pi, w x*h x) = 0 := by
    have he := (wp.mul hp).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hi
  have hcos : (∫ x in α..α+2*Real.pi, w x*h x*Real.cos x) = 0 := by
    have he := ((wp.mul hp).mul Real.cos_periodic).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hm.1
  have hsin : (∫ x in α..α+2*Real.pi, w x*h x*Real.sin x) = 0 := by
    have he := ((wp.mul hp).mul Real.sin_periodic).intervalIntegral_add_eq α 0
    simp only [zero_add,Pi.mul_apply] at he
    exact he.trans hm.2
  obtain ⟨x,y,z,hx,hz,hxy,hyz,hpx,hny,hpz⟩ :=
    moment_sign_changes hc wc α (fun x _ => hw x) hα hα' hposI hi' hcos hsin
  exact PlanarTopology.angles_no_alternation hu hpos hneg hx.1 hxy hyz hz.2 hα hpx hny hpz

end StrictHotSpots.CircleSigns
end DiskBoundaryMomentsLayer

section DiskMultiplicityLayer
open Set MeasureTheory Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots.CircleSigns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem disk_family_finrank_le_two_oai (F : ℂ → E)
    (hc : ContinuousOn F (closedBall 0 1))
    (hb : ∀ a : E, a ≠ 0 → ∃ s : Circle, 0 < inner ℝ a (F s))
    (hp : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | 0 < inner ℝ a (F z)}))
    (hn : ∀ a : E, a ≠ 0 → IsConnected
      (ball (0:ℂ) 1 ∩ {z | inner ℝ a (F z) < 0})) : finrank ℝ E ≤ 2 := by
  let G : C(Circle,E) := ⟨fun s => F s,
    hc.comp_continuous (by fun_prop) (fun s => by simpa only [mem_closedBall,dist_zero_right,Circle.norm_coe] using (le_refl (1:ℝ)))⟩
  obtain ⟨w,wc,wp,hw,hzero⟩ := PositiveWeight.exists_circle_weight G hb
  let T : E →ₗ[ℝ] ℝ×ℝ := (weightedMoment F w Real.cos (wc.mul Real.continuous_cos) hc).prod
    (weightedMoment F w Real.sin (wc.mul Real.continuous_sin) hc)
  have hker (a : E) (ha : T a = 0) : a = 0 := by
    by_contra haz
    obtain ⟨s,hs⟩ := hb a haz
    have hne : ∃ θ, inner ℝ a (F (Circle.exp θ : ℂ)) ≠ 0 := by
      exact ⟨(s:ℂ).arg,by simpa only [Circle.exp_arg] using ne_of_gt hs⟩
    have hcont : ContinuousOn (fun z => inner ℝ a (F z)) (closedBall 0 1) :=
      continuousOn_const.inner hc
    have hh := disk_moments_nonzero hcont (hp a haz) (hn a haz) wc wp hw hne (hzero a)
    have hreal := congrArg Prod.fst ha
    have himag := congrArg Prod.snd ha
    change (∫ θ in (0:ℝ)..2*Real.pi, w θ*Real.cos θ*inner ℝ a (F (Circle.exp θ : ℂ))) = 0 at hreal
    change (∫ θ in (0:ℝ)..2*Real.pi, w θ*Real.sin θ*inner ℝ a (F (Circle.exp θ : ℂ))) = 0 at himag
    have hre : (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ : ℂ))*Real.cos θ) = 0 := by
      simpa only [mul_right_comm (w _) (Real.cos _) _] using hreal
    have him : (∫ θ in (0:ℝ)..2*Real.pi, w θ*inner ℝ a (F (Circle.exp θ : ℂ))*Real.sin θ) = 0 := by
      simpa only [mul_right_comm (w _) (Real.sin _) _] using himag
    exact hh.elim (fun h => h hre) (fun h => h him)
  have hi : Injective T := by
    intro a b he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,he,sub_self]
  simpa only [finrank_prod,finrank_self] using T.finrank_le_finrank_of_injective hi
end StrictHotSpots.CircleSigns
end DiskMultiplicityLayer
end
end MultiplicityComplete


end OAI
end

theorem solution.{u_1} : type_of% @OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two_oai.{u_1} := @OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two_oai.{u_1}
