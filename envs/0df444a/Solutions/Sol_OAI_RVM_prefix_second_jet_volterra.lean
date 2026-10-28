-- Prove2me | solution 1 for OAI.RVM.prefix_second_jet_volterra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:42:23.269919+00:00
-- url     : https://prove2.me/submissions/04b9dcb8-a13b-4dab-ba90-254cdffcdade

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_classical_fields_curvature_volterra_bound

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    convert hT.deriv using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma hasDerivAt_particle_along_curve {f : Particle} {X V : ℝ → Vec}
    {t : ℝ} {u K : Vec} (hf : DifferentiableAt ℝ f (t,X t,V t))
    (hX : HasDerivAt X u t) (hV : HasDerivAt V K t) :
    HasDerivAt (fun s => f (s,X s,V s))
      (deriv (fun s => f (s,X t,V t)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,V t)) (X t) i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,X t,v')) (V t) i)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hX.prodMk hV))
  rw [full_directional_derivative hf] at h
  exact h

lemma particle_differentiableAt_positive {s : Solution}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    DifferentiableAt ℝ s.f (t,x,v) := by
  have hnhds : particleHalfSpace ∈ nhds (t,x,v) := by
    have hopen : IsOpen {z : ℝ × Phase | 0 < z.1} :=
      isOpen_lt continuous_const continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds ht)
    intro z hz
    change 0 ≤ z.1
    exact le_of_lt hz
  exact ((hreg (t,x,v) ht.le).contDiffAt hnhds).differentiableAt (by norm_num)

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma fderiv_q_apply (v h : Vec) : fderiv ℝ q v h = dot (velocity v) h := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt q (fderiv ℝ q v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_energy hc
  have he := h₁.unique h₂
  simpa using he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_LorentzPhase
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise
open Set MeasureTheory Filter
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open Set MeasureTheory
open scoped ContDiff

open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_bounded_ode_on_Icc {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {f : ℝ × H → H}
    {a b t₀ L : ℝ} (hab : a ≤ b) (ht₀ : t₀ ∈ Icc a b) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ 1 f (Icc a b ×ˢ (univ : Set H)))
    (hb : ∀ t ∈ Icc a b, ∀ z, ‖f (t,z)‖ ≤ L) (z₀ : H) :
    ∃ α : ℝ → H, α t₀ = z₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt α (f (t,α t)) (Icc a b) t := by
  let R : ℝ≥0 := ⟨L*(b-a),mul_nonneg hL (sub_nonneg.mpr hab)⟩
  have hsub : Icc a b ×ˢ closedBall z₀ (R:ℝ) ⊆ Icc a b ×ˢ (univ : Set H) :=
    prod_mono_right (subset_univ _)
  obtain ⟨K,hK⟩ := (hf.mono hsub).exists_lipschitzOnWith (by norm_num)
    ((convex_Icc a b).prod (convex_closedBall z₀ (R:ℝ)))
    (isCompact_Icc.prod (isCompact_closedBall z₀ (R:ℝ)))
  have hpic : IsPicardLindelof (fun t z => f (t,z)) ⟨t₀,ht₀⟩ z₀ R 0 ⟨L,hL⟩ K := by
    refine ⟨?_,?_,?_,?_⟩
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      simpa using hK.dist_le_mul (t,z) (show (t,z) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hz⟩)
        (t,w) (show (t,w) ∈ Icc a b ×ˢ closedBall z₀ (R:ℝ) from ⟨ht,hw⟩)
    · intro z _
      exact hf.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        (fun t ht => ⟨ht,mem_univ z⟩)
    · intro t ht z _
      exact hb t ht z
    · change L * max (b-t₀) (t₀-a) ≤ (R:ℝ)-0
      simp only [sub_zero]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht₀.1]) (by linarith [ht₀.2])) hL
  exact hpic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma cutLorentz_regular {E B : Field} {χ : Vec → ℝ} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hχ : ContDiff ℝ 1 χ) :
    ContDiffOn ℝ 1 (cutLorentz E B χ) (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hx : ContDiff ℝ 1 (fun p : ℝ × Phase => (p.1,p.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hm : MapsTo (fun p : ℝ × Phase => (p.1,p.2.1))
      (Icc 0 T ×ˢ (univ : Set Phase)) fieldHalfSpace := fun _ hp => hp.1.1
  have hu : ContDiff ℝ 1 (fun p : ℝ × Phase => velocity p.2.2) :=
    contDiff_velocity.comp (contDiff_snd.comp contDiff_snd)
  exact hu.contDiffOn.prodMk
    ((hχ.comp (contDiff_fst.comp contDiff_snd)).contDiffOn.smul
      ((hE.comp hx.contDiffOn hm).add
        (contDiff_cross.contDiffOn.comp (hu.contDiffOn.prodMk (hB.comp hx.contDiffOn hm))
          (mapsTo_univ _ _))))

lemma cutLorentz_bounded {E B : Field} {T : ℝ} (_hT : 0 ≤ T) {x₀ : Vec}
    (hE : ContinuousOn E fieldHalfSpace) (hB : ContinuousOn B fieldHalfSpace)
    (χ : ContDiffBump x₀) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Icc 0 T, ∀ z, ‖cutLorentz E B χ (t,z)‖ ≤ L := by
  have hsub : Icc 0 T ×ˢ closedBall x₀ χ.rOut ⊆ fieldHalfSpace := fun _ hp => hp.1.1
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ χ.rOut)).bddAbove_image
    ((hE.norm.add hB.norm).mono hsub)
  refine ⟨max 1 M, (zero_le_one.trans (le_max_left _ _)),?_⟩
  intro t ht z
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_velocity_lt_one z.2).le.trans (le_max_left _ _)
  change ‖χ z.1 • (E (t,z.1)+cross (velocity z.2) (B (t,z.1)))‖ ≤ max 1 M
  by_cases hχ : χ z.1 = 0
  · simp only [hχ,zero_smul,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)
  have hz : z.1 ∈ closedBall x₀ χ.rOut := ball_subset_closedBall (by
    rw [← χ.support_eq]
    exact hχ)
  calc
    _ = χ z.1 * ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ := by
      rw [norm_smul,Real.norm_of_nonneg χ.nonneg]
    _ ≤ ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) χ.le_one
    _ ≤ ‖E (t,z.1)‖+‖B (t,z.1)‖ := by
      have hc : ‖cross (velocity z.2) (B (t,z.1))‖ ≤ ‖B (t,z.1)‖ :=
        (norm_cross_le (velocity z.2) (B (t,z.1))).trans
          (mul_le_of_le_one_left (norm_nonneg (B (t,z.1))) (norm_velocity_lt_one z.2).le)
      exact (norm_add_le (E (t,z.1)) (cross (velocity z.2) (B (t,z.1)))).trans
        (add_le_add le_rfl hc)
    _ ≤ M := hM ⟨(t,z.1),⟨ht,hz⟩,rfl⟩
    _ ≤ _ := le_max_right _ _

lemma exists_characteristic_on_slab {E B : Field} {T t₀ : ℝ} (hT : 0 ≤ T)
    (ht₀ : t₀ ∈ Icc 0 T) (hE : ContDiffOn ℝ 1 E fieldHalfSpace)
    (hB : ContDiffOn ℝ 1 B fieldHalfSpace) (x₀ v₀ : Vec) :
    ∃ X V : ℝ → Vec, X t₀=x₀ ∧ V t₀=v₀ ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt X (velocity (V t)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt V
        (E (t,X t)+cross (velocity (V t)) (B (t,X t))) (Icc 0 T) t) ∧
      LipschitzOnWith 1 X (Icc 0 T) := by
  let χ : ContDiffBump x₀ := ⟨T+1,T+2,by linarith,by linarith⟩
  obtain ⟨L,hL,hbound⟩ := cutLorentz_bounded hT hE.continuousOn hB.continuousOn χ
  obtain ⟨α,hα₀,hα⟩ := exists_bounded_ode_on_Icc hT ht₀ hL
    (cutLorentz_regular hE hB χ.contDiff) hbound (x₀,v₀)
  have hX : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun r => (α r).1)
      (velocity (α t).2) (Icc 0 T) t := fun t ht => (hα t ht).fst
  have hLip : LipschitzOnWith 1 (fun r => (α r).1) (Icc 0 T) :=
    (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hX
      (fun t _ => by exact_mod_cast (norm_velocity_lt_one (α t).2).le)
  have hone : ∀ t ∈ Icc 0 T, χ (α t).1=1 := by
    intro t ht
    apply χ.one_of_mem_closedBall
    have hdist := hLip.dist_le_mul t ht t₀ ht₀
    simp only [hα₀,NNReal.coe_one,one_mul] at hdist
    change dist (α t).1 x₀ ≤ T+1
    have hd : dist t t₀ ≤ T := by
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [ht.1,ht.2,ht₀.1,ht₀.2]
    linarith
  refine ⟨(fun r => (α r).1),(fun r => (α r).2),congrArg Prod.fst hα₀,
    congrArg Prod.snd hα₀,hX,?_,hLip⟩
  intro t ht
  have hv : HasDerivWithinAt (fun r => (α r).2)
      (χ (α t).1 • (E (t,(α t).1)+cross (velocity (α t).2) (B (t,(α t).1)))) (Icc 0 T) t :=
    (hα t ht).snd
  simpa only [hone t ht,one_smul] using hv

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma velocityProjection_norm (u b : Vec) (hu : ‖u‖ ≤ 1) :
    ‖velocityProjection u b‖ ≤ ‖b‖ := by
  have hsq : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : ‖velocityProjection u b‖^2 =
      ‖b‖^2 - 2*(dot u b)^2+(dot u b)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm b u]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (dot u b))
  nlinarith [norm_nonneg (velocityProjection u b), norm_nonneg b]

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_IncrementBootstrap
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma norm_fderiv_q_le (v : Vec) : ‖fderiv ℝ q v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  rw [fderiv_q_apply,Real.norm_eq_abs,one_mul]
  calc
    _ ≤ ‖velocity v‖ * ‖h‖ := by simpa only [dot_eq_inner] using abs_real_inner_le_norm (velocity v) h
    _ ≤ ‖h‖ := mul_le_of_le_one_left (norm_nonneg h) (norm_velocity_lt_one v).le

lemma q_lipschitz (v w : Vec) : |q w-q v| ≤ ‖w-v‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) x)
    (fun x _ => norm_fderiv_q_le x) (mem_univ v) (mem_univ w)
  simpa only [Real.norm_eq_abs,one_mul] using h

lemma norm_relativistic_projection_le (u h : Vec) (hu : ‖u‖ ≤ 1) :
    ‖h-dot u h • u‖ ≤ ‖h‖ := by
  have hsq : ‖h-dot u h • u‖^2 = ‖h‖^2-2*(dot u h)^2+(dot u h)^2*‖u‖^2 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← dot_eq_inner,
      dot_smul_right,dot_comm h u]
    ring
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (dot u h))
  nlinarith [norm_nonneg (h-dot u h • u),norm_nonneg h,sq_nonneg (dot u h)]

lemma norm_fderiv_velocity_le (v : Vec) : ‖fderiv ℝ velocity v‖ ≤ (q v)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (q_pos v).le)
  intro h
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos v))]
  exact mul_le_mul_of_nonneg_left
    (norm_relativistic_projection_le _ _ (norm_velocity_lt_one v).le)
    (inv_nonneg.mpr (q_pos v).le)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PositiveExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_positiveTimeCut (a : ℝ) : ContDiff ℝ ∞ (positiveTimeCut a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (a/4))
lemma positiveTimeCut_zero {a t : ℝ} (ha : 0<a) (ht : t≤a/4) : positiveTimeCut a t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
lemma positiveTimeCut_one {a t : ℝ} (ha : 0<a) (ht : a/2≤t) : positiveTimeCut a t=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0<a/4)).mpr
  linarith

end PositiveExtension

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma smooth_compact_lipschitz {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, ‖f y-f x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := (hf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z _ => (hD z).trans (le_max_left _ _)) (mem_univ x) (mem_univ y)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma velocity_global_lipschitz (v w : Vec) : ‖velocity w-velocity v‖≤‖w-v‖ := by
  have hh := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (contDiff_velocity (k:=1)).differentiable (by norm_num) x)
    (C:=1) (fun x _ => (norm_fderiv_velocity_le x).trans ((inv_le_one₀ (q_pos x)).mpr (by
      have hq := q_sq x
      nlinarith [q_pos x,sq_nonneg ‖x‖]))) (mem_univ v) (mem_univ w)
  simpa only [one_mul] using hh

lemma lorentzField_difference_bound {E B E' B' : Field} {t L N D : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (hB : ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ x, ‖B (t,x)-B' (t,x)‖≤D) (z z' : Phase) :
    ‖lorentzField E B (t,z)-lorentzField E' B' (t,z')‖≤(1+2*N+L)*‖z-z'‖+2*D := by
  have hpos : ‖z.1-z'.1‖≤‖z-z'‖ := by simpa only [Prod.fst_sub] using norm_fst_le (z-z')
  have hvel : ‖z.2-z'.2‖≤‖z-z'‖ := by simpa only [Prod.snd_sub] using norm_snd_le (z-z')
  have hu : ‖velocity z.2‖≤1 := (norm_velocity_lt_one _).le
  have hu' : ‖velocity z'.2‖≤1 := (norm_velocity_lt_one _).le
  have hUd : ‖velocity z.2-velocity z'.2‖≤‖z-z'‖ := (velocity_global_lipschitz z'.2 z.2).trans hvel
  have hF : ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
      (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))‖≤(2*N+L)*‖z-z'‖+2*D := by
    have he : E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
        (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))=
        (E (t,z.1)-E (t,z'.1))+(E (t,z'.1)-E' (t,z'.1))+
        cross (velocity z.2-velocity z'.2) (B (t,z.1))+
        cross (velocity z'.2) (B (t,z.1)-B (t,z'.1))+
        cross (velocity z'.2) (B (t,z'.1)-B' (t,z'.1)) := by
      rw [cross_sub_left,cross_sub_right,cross_sub_right]
      abel
    rw [he]
    have h₁ := (hEx z'.1 z.1).trans (mul_le_mul_of_nonneg_left hpos hN)
    have h₂ := hEd z'.1
    have h₃ := (norm_cross_le _ _).trans (mul_le_mul hUd (hB z.1) (norm_nonneg _) (norm_nonneg _))
    have h₄ := (norm_cross_le _ _).trans (mul_le_mul hu' ((hBx z'.1 z.1).trans
      (mul_le_mul_of_nonneg_left hpos hN)) (norm_nonneg _) zero_le_one)
    have h₅ := (norm_cross_le _ _).trans (mul_le_mul hu' (hBd z'.1) (norm_nonneg _) zero_le_one)
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)) h₅)
    exact hh.trans_eq (by ring)
  simp only [lorentzField]
  rw [Prod.norm_def]
  simp only [Prod.fst_sub,Prod.snd_sub]
  apply max_le
  · exact hUd.trans (by nlinarith [norm_nonneg (z-z')])
  · exact hF.trans (by nlinarith [norm_nonneg (z-z')])

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma taylor_remainder_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) (x y : U) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖≤H*‖y-x‖^2 := by
  have h := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
    (f:=f) (φ:=fderiv ℝ f x) (C:=H*‖y-x‖) (fun z _ => hf z)
    (fun z hz => (hD x z).trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_eq_norm] using hz) hH))
    (show x∈closedBall x ‖y-x‖ by simp)
    (show y∈closedBall x ‖y-x‖ by simp only [mem_closedBall,dist_eq_norm,le_refl])
  exact h.trans_eq (by ring)

lemma curvature_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) : CurvatureBound f (2*H) := by
  intro x v
  have hp := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x+v)
  have hm := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x-v)
  simp only [add_sub_cancel_left,sub_sub_cancel_left,norm_neg,map_neg] at hp hm
  have he : f (x+v)+f (x-v)-(2:ℝ) • f x =
      (f (x+v)-f x-fderiv ℝ f x v)+(f (x-v)-f x+fderiv ℝ f x v) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hp (by simpa only [sub_neg_eq_add] using hm))).trans_eq (by ring)

lemma smooth_compact_curvature {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ H : ℝ, 0≤H ∧ CurvatureBound f H := by
  obtain ⟨H,hH,hD⟩ := smooth_compact_lipschitz
    (hf.fderiv_right (by decide)) (hc.fderiv ℝ)
  exact ⟨2*H,by positivity,curvature_of_fderiv_lipschitz (hf.differentiable (by simp)) hH hD⟩

lemma CurvatureBound.triple {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H L : ℝ} (hc : CurvatureBound f H) (hH : 0≤H) (_hL : 0≤L)
    (hl : ∀ x y, ‖f y-f x‖≤L*‖y-x‖) (a b c : U) :
    ‖f a+f b-(2:ℝ) • f c‖≤H*‖a-b‖^2+L*‖a+b-(2:ℝ) • c‖ := by
  let m := (1/2:ℝ) • (a+b)
  let v := (1/2:ℝ) • (a-b)
  have hp : m+v=a := by dsimp [m,v]; module
  have hm : m-v=b := by dsimp [m,v]; module
  have hb := hc m v
  rw [hp,hm] at hb
  have hv : ‖v‖≤‖a-b‖ := by dsimp [v]; rw [norm_smul,Real.norm_eq_abs]; norm_num; nlinarith [norm_nonneg (a-b)]
  have hmd : (2:ℝ) • (m-c)=a+b-(2:ℝ) • c := by dsimp [m]; module
  have hde : f a+f b-(2:ℝ) • f c =
      (f a+f b-(2:ℝ) • f m)+(2:ℝ) • (f m-f c) := by module
  rw [hde]
  have hh := hl c m
  have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)
  have hscale : 2*‖m-c‖=‖a+b-(2:ℝ) • c‖ := by rw [← hmd,norm_smul,Real.norm_eq_abs]; norm_num
  have hscale' := congrArg (fun r : ℝ => L*r) hscale
  have hnorm : ‖(2:ℝ) • (f m-f c)‖≤L*‖a+b-(2:ℝ) • c‖ := by
    rw [norm_smul,Real.norm_eq_abs]; norm_num
    nlinarith [hh',hscale']
  exact (norm_add_le _ _).trans (add_le_add (hb.trans
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hv) hH)) hnorm)

lemma inverse_q_lipschitz (v w : Vec) : |(q w)⁻¹-(q v)⁻¹|≤‖w-v‖ := by
  have hv : 1≤q v := by nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  have hw : 1≤q w := by nlinarith [q_sq w,q_pos w,sq_nonneg ‖w‖]
  have he : (q w)⁻¹-(q v)⁻¹=(q v-q w)/(q w*q v) := by field_simp
  rw [he,abs_div,abs_of_pos (mul_pos (q_pos w) (q_pos v)),abs_sub_comm]
  exact (div_le_self (abs_nonneg _) (by nlinarith : 1≤q w*q v)).trans (q_lipschitz v w)

lemma velocityProjection_parameter_lipschitz {u v : Vec} (hu : ‖u‖≤1) (hv : ‖v‖≤1) (h : Vec) :
    ‖velocityProjection u h-velocityProjection v h‖≤2*‖u-v‖*‖h‖ := by
  have he : velocityProjection u h-velocityProjection v h=
      -(dot (u-v) h • u+dot v h • (u-v)) := by
    simp only [velocityProjection,dot_sub_left,sub_smul,smul_sub]
    module
  rw [he,norm_neg]
  have h₁ : ‖dot (u-v) h • u‖≤‖u-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (abs_dot_le _ _) hu (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h₂ : ‖dot v h • (u-v)‖≤‖u-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_right ((abs_dot_le v h).trans
      (mul_le_mul_of_nonneg_right hv (norm_nonneg h))) (norm_nonneg (u-v))
    exact hh.trans_eq (by ring)
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)

lemma fderiv_velocity_lipschitz (v w : Vec) :
    ‖fderiv ℝ velocity w-fderiv ℝ velocity v‖≤3*‖w-v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  have hu := (norm_velocity_lt_one w).le
  have hv := (norm_velocity_lt_one v).le
  have hh : (1:ℝ)≤q v := by nlinarith [q_sq v,q_pos v,sq_nonneg ‖v‖]
  have hq : 0≤(q v)⁻¹ := inv_nonneg.mpr (q_pos v).le
  have hq1 : (q v)⁻¹≤1 := (inv_le_one₀ (q_pos v)).mpr hh
  have he : (fderiv ℝ velocity w-fderiv ℝ velocity v) h =
      ((q w)⁻¹-(q v)⁻¹) • velocityProjection (velocity w) h+
      (q v)⁻¹ • (velocityProjection (velocity w) h-velocityProjection (velocity v) h) := by
    simp only [sub_apply,fderiv_velocity_apply,velocityProjection,sub_smul,smul_sub]
    module
  rw [he]
  have h₁ : ‖((q w)⁻¹-(q v)⁻¹) • velocityProjection (velocity w) h‖≤‖w-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (inverse_q_lipschitz v w) (velocityProjection_norm _ _ hu)
      (norm_nonneg _) (norm_nonneg _)
  have h₂ : ‖(q v)⁻¹ • (velocityProjection (velocity w) h-velocityProjection (velocity v) h)‖≤
      2*‖w-v‖*‖h‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq]
    have hp := (velocityProjection_parameter_lipschitz hu hv h).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (velocity_global_lipschitz v w)
        (by norm_num)) (norm_nonneg h))
    exact (mul_le_mul hq1 hp (norm_nonneg _) zero_le_one).trans_eq (by ring)
  exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)

lemma velocity_curvature : CurvatureBound velocity 6 := by
  convert curvature_of_fderiv_lipschitz
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0)) (by norm_num : (0:ℝ)≤3)
    fderiv_velocity_lipschitz using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

lemma CurvatureBound.precomp_linear {U V W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : V → W} {H : ℝ}
    (hf : CurvatureBound f H) (hH : 0≤H) (A : U →L[ℝ] V) (hA : ∀ v, ‖A v‖≤‖v‖) :
    CurvatureBound (f ∘ A) H := by
  intro x v
  simp only [Function.comp_def,map_add,map_sub]
  exact (hf (A x) (A v)).trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hA v)) hH)

lemma CurvatureBound.add {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x+g x) (H+K) := by
  intro x v
  have he : f (x+v)+g (x+v)+(f (x-v)+g (x-v))-(2:ℝ) • (f x+g x)=
      (f (x+v)+f (x-v)-(2:ℝ) • f x)+(g (x+v)+g (x-v)-(2:ℝ) • g x) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (hf x v) (hg x v))).trans_eq (by ring)

lemma CurvatureBound.cross_product {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {f g : U → Vec} {A B L N H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K)
    (hA : 0≤A) (_hB : 0≤B) (hL : 0≤L) (_hN : 0≤N) (hH : 0≤H) (_hK : 0≤K)
    (hfb : ∀ x, ‖f x‖≤A) (hgb : ∀ x, ‖g x‖≤B)
    (hfl : ∀ x y, ‖f y-f x‖≤L*‖y-x‖) (hgl : ∀ x y, ‖g y-g x‖≤N*‖y-x‖) :
    CurvatureBound (fun x => cross (f x) (g x)) (H*B+A*K+2*L*N) := by
  intro x v
  have he : cross (f (x+v)) (g (x+v))+cross (f (x-v)) (g (x-v))-
      (2:ℝ) • cross (f x) (g x)=
      cross (f (x+v)+f (x-v)-(2:ℝ) • f x) (g x)+
      cross (f x) (g (x+v)+g (x-v)-(2:ℝ) • g x)+
      cross (f (x+v)-f x) (g (x+v)-g x)+cross (f (x-v)-f x) (g (x-v)-g x) := by
    ext i
    fin_cases i <;> simp [cross] <;> ring
  have h₁ := (norm_cross_le _ _).trans (mul_le_mul (hf x v) (hgb x) (norm_nonneg _) (by positivity))
  have h₂ := (norm_cross_le _ _).trans (mul_le_mul (hfb x) (hg x v) (norm_nonneg _) hA)
  have h₃ : ‖cross (f (x+v)-f x) (g (x+v)-g x)‖≤(L*‖v‖)*(N*‖v‖) := by
    have hp := hfl x (x+v)
    have hq := hgl x (x+v)
    simp only [add_sub_cancel_left] at hp hq
    exact (norm_cross_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (by positivity))
  have h₄ : ‖cross (f (x-v)-f x) (g (x-v)-g x)‖≤(L*‖v‖)*(N*‖v‖) := by
    have hp := hfl x (x-v)
    have hq := hgl x (x-v)
    simp only [sub_sub_cancel_left,norm_neg] at hp hq
    exact (norm_cross_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (by positivity))
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)).trans_eq (by ring)

lemma lorentzField_curvature {E B : Field} {t L N H : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hH : 0≤H)
    (hBb : ∀ x, ‖B (t,x)‖≤L)
    (hBx : ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEc : CurvatureBound (fun x => E (t,x)) H)
    (hBc : CurvatureBound (fun x => B (t,x)) H) :
    CurvatureBound (fun z => lorentzField E B (t,z)) (6+6*L+2*H+2*N) := by
  let u : Phase → Vec := fun z => velocity z.2
  let g : Phase → Vec := fun z => B (t,z.1)
  have hu : CurvatureBound u 6 := velocity_curvature.precomp_linear (by norm_num)
    (ContinuousLinearMap.snd ℝ Vec Vec) (fun z => norm_snd_le z)
  have hg : CurvatureBound g H := hBc.precomp_linear hH
    (ContinuousLinearMap.fst ℝ Vec Vec) (fun z => norm_fst_le z)
  have he : CurvatureBound (fun z : Phase => E (t,z.1)) H := hEc.precomp_linear hH
    (ContinuousLinearMap.fst ℝ Vec Vec) (fun z => norm_fst_le z)
  have hul (z w : Phase) : ‖u w-u z‖≤1*‖w-z‖ := by
    change ‖velocity w.2-velocity z.2‖≤1*‖w-z‖
    rw [one_mul]
    exact (velocity_global_lipschitz z.2 w.2).trans (norm_snd_le (w-z))
  have hgl (z w : Phase) : ‖g w-g z‖≤N*‖w-z‖ :=
    (hBx z.1 w.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le (w-z)) hN)
  have hc := hu.cross_product hg (by norm_num) hL (by norm_num) hN (by norm_num) hH
    (fun z => (norm_velocity_lt_one z.2).le) (fun z => hBb z.1) hul hgl
  have hforce := he.add hc
  intro z v
  change ‖(u (z+v),E (t,(z+v).1)+cross (u (z+v)) (g (z+v)))+
    (u (z-v),E (t,(z-v).1)+cross (u (z-v)) (g (z-v)))-
    (2:ℝ) • (u z,E (t,z.1)+cross (u z) (g z))‖≤_
  rw [Prod.norm_def,max_le_iff]
  constructor
  · have hh := hu z v
    simp only [Prod.fst_sub,Prod.fst_add,Prod.smul_fst]
    nlinarith [hh,sq_nonneg ‖v‖,mul_nonneg hL (sq_nonneg ‖v‖),
      mul_nonneg hH (sq_nonneg ‖v‖),mul_nonneg hN (sq_nonneg ‖v‖)]
  · have hh := hforce z v
    simp only [Prod.snd_sub,Prod.snd_add,Prod.smul_snd]
    nlinarith [hh,sq_nonneg ‖v‖]

lemma CurvatureBound.mono {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H K : ℝ} (hf : CurvatureBound f H) (h : H≤K) : CurvatureBound f K :=
  fun x v => (hf x v).trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))

lemma CurvatureBound.spatial_slice {f : Phase → ℝ} {H : ℝ}
    (hf : CurvatureBound f H) (v : Vec) : CurvatureBound (fun x => f (x,v)) H := by
  intro x h
  simpa only [Prod.mk_add_mk,Prod.mk_sub_mk,add_zero,sub_zero,Prod.norm_mk,norm_zero,
    max_eq_left (norm_nonneg _)] using hf (x,v) (h,0)

lemma curvature_of_second_derivative_bound {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : ContDiff ℝ ∞ f) {H : ℝ} (hH : 0≤H)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖≤H) : CurvatureBound f (2*H) := by
  apply curvature_of_fderiv_lipschitz (hf.differentiable (by simp)) hH
  intro x y
  apply (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.fderiv_right (by decide : (1:ℕ∞ω)+1≤∞)).differentiable (by norm_num) z) _ (mem_univ _) (mem_univ _)
  intro z _
  simpa only [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv] using hb z

end

section

open Set Filter MeasureTheory
open scoped Topology

lemma variable_integral_gronwall_bound {f b : ℝ → ℝ} (hf : Continuous f)
    (hb : Continuous b) {a T : ℝ} (hb0 : ∀ t∈Icc (0:ℝ) T,0≤b t)
    (hbound : ∀ t∈Icc (0:ℝ) T,f t≤a+∫ r in 0..t,b r*f r) :
    ∀ t∈Icc (0:ℝ) T,f t≤a*Real.exp (∫ r in 0..t,b r) := by
  let G : ℝ → ℝ := fun t => a+∫ r in 0..t,b r*f r
  let B : ℝ → ℝ := fun t => ∫ r in 0..t,b r
  have hG : Continuous G := continuous_const.add
    (intervalIntegral.continuous_primitive (hb.mul hf).intervalIntegrable 0)
  have hB : Continuous B := intervalIntegral.continuous_primitive hb.intervalIntegrable 0
  have hdG (t : ℝ) : HasDerivAt G (b t*f t) t := by
    exact (intervalIntegral.integral_hasDerivAt_right ((hb.mul hf).intervalIntegrable 0 t)
      (hb.mul hf).stronglyMeasurable.stronglyMeasurableAtFilter (hb.mul hf).continuousAt).const_add a
  have hdB (t : ℝ) : HasDerivAt B (b t) t :=
    intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable 0 t)
      hb.stronglyMeasurable.stronglyMeasurableAtFilter hb.continuousAt
  let H : ℝ → ℝ := fun t => Real.exp (-B t)*G t
  have hdH (t : ℝ) : HasDerivAt H
      (Real.exp (-B t)*(b t*f t-b t*G t)) t := by
    have hd := ((hdB t).neg.exp.mul (hdG t))
    change HasDerivAt H ((Real.exp (-B t))*(-b t)*G t+Real.exp (-B t)*(b t*f t)) t at hd
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmono : AntitoneOn H (Icc (0:ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (((Real.continuous_exp.comp hB.neg).mul hG).continuousOn) (fun t ht => (hdH t).differentiableAt.differentiableWithinAt)
    intro t ht
    change deriv H t ≤ 0
    rw [(hdH t).deriv]
    have ht' : t∈Icc (0:ℝ) T := interior_subset ht
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left (hbound t ht') (hb0 t ht'))
  intro t ht
  have hh := hmono (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,ht.1.trans ht.2⟩) ht ht.1
  have hh' : Real.exp (-B t)*G t≤a := by
    simpa only [H,G,B,intervalIntegral.integral_same,add_zero,neg_zero,Real.exp_zero,one_mul] using hh
  have hs := mul_le_mul_of_nonneg_left hh' (Real.exp_pos (B t)).le
  have he : Real.exp (B t)*(Real.exp (-B t)*G t)=G t := by
    rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  rw [he] at hs
  exact (hbound t ht).trans (by simpa only [G,B,mul_comm] using hs)

lemma variable_integral_gronwall_bound_on {f b : ℝ → ℝ} {a T : ℝ} (hT : 0≤T)
    (hf : ContinuousOn f (Icc (0:ℝ) T)) (hb : ContinuousOn b (Icc (0:ℝ) T))
    (hb0 : ∀ t∈Icc (0:ℝ) T,0≤b t)
    (hbound : ∀ t∈Icc (0:ℝ) T,f t≤a+∫ r in 0..t,b r*f r) :
    ∀ t∈Icc (0:ℝ) T,f t≤a*Real.exp (∫ r in 0..t,b r) := by
  let p : ℝ → ℝ := fun r => max 0 (min T r)
  have hp : ∀ r, p r∈Icc (0:ℝ) T := fun r =>
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have he (r : ℝ) (hr : r∈Icc (0:ℝ) T) : p r=r := by
    dsimp [p]; rw [min_eq_right hr.2,max_eq_right hr.1]
  have hcp : Continuous p := by fun_prop
  have hh := variable_integral_gronwall_bound
    (hf.comp_continuous hcp hp) (hb.comp_continuous hcp hp)
    (fun r hr => hb0 (p r) (hp r)) (a:=a) (T:=T) (fun r hr => by
      simpa only [Function.comp_apply,he r hr] using (hbound r hr).trans_eq
        (congrArg (a+·) (intervalIntegral.integral_congr (fun u hu => by
          have hu' : u∈Icc (0:ℝ) T := ⟨(uIcc_of_le hr.1 ▸ hu).1,(uIcc_of_le hr.1 ▸ hu).2.trans hr.2⟩
          simp only [he u hu']))))
  intro t ht
  have hi : (∫ r in 0..t,(b ∘ p) r)=∫ r in 0..t,b r :=
    intervalIntegral.integral_congr (fun r hr => by
      have hr' : r∈Icc (0:ℝ) T := ⟨(uIcc_of_le ht.1 ▸ hr).1,(uIcc_of_le ht.1 ▸ hr).2.trans ht.2⟩
      simp only [Function.comp_apply,he r hr'])
  have hout := hh t ht
  rw [hi] at hout
  simpa only [Function.comp_apply,he t ht] using hout

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_ode_volterra_bound {z dz : ℝ → E} {b : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hb : ContinuousOn b (Icc (0:ℝ) T)) (hb0 : ∀ r∈Icc (0:ℝ) T,0≤b r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤b r*‖z r‖) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤‖z 0‖*Real.exp (∫ r in 0..t,b r) := by
  apply variable_integral_gronwall_bound_on hT hz.norm hb hb0
  intro t ht
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
  have hi : IntervalIntegrable dz volume 0 t := (hdz.mono hsub).intervalIntegrable_of_Icc ht.1
  have he : ∫ r in 0..t,dz r=z t-z 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hz.mono hsub)
      (fun r hr => hder r ⟨hr.1,hr.2.trans_le ht.2⟩) hi
  calc
    ‖z t‖ = ‖z 0+∫ r in 0..t,dz r‖ := by rw [he]; congr 1; abel
    _ ≤ ‖z 0‖+∫ r in 0..t,‖dz r‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1))
    _ ≤ ‖z 0‖+∫ r in 0..t,b r*‖z r‖ := by
      apply add_le_add le_rfl
      apply intervalIntegral.integral_mono_on ht.1 hi.norm
        (((hb.mul hz.norm).mono hsub).intervalIntegrable_of_Icc ht.1)
      exact fun r hr => hbound r (hsub hr)

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

lemma transport_on_characteristic_before {s : Solution} {X V : ℝ → Vec} {T U : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s U)
    (hT : 0≤T) (hTU : T≤U)
    (hXc : ContinuousOn X (Icc 0 T)) (hVc : ContinuousOn V (Icc 0 T))
    (hX : ∀ t∈Ioo 0 T,HasDerivAt X (velocity (V t)) t)
    (hV : ∀ t∈Ioo 0 T,HasDerivAt V (s.E (t,X t)+cross (velocity (V t)) (s.B (t,X t))) t) :
    s.f (T,X T,V T)=s.f (0,X 0,V 0) := by
  rcases hT.eq_or_lt with h|h
  · simp [←h]
  have hc : ContinuousOn (fun t => s.f (t,X t,V t)) (Icc 0 T) :=
    hf.continuousOn.comp (continuousOn_id.prodMk (hXc.prodMk hVc)) (fun t ht => ht.1)
  have hd : ∀ t∈Ioo 0 T,HasDerivAt (fun r => s.f (r,X r,V r)) (0:ℝ) t := by
    intro t ht
    have hder := hasDerivAt_particle_along_curve
      (particle_differentiableAt_positive hf ht.1 (X t) (V t)) (hX t ht) (hV t ht)
    have hpde := (heq t ht.1.le (ht.2.trans_le hTU)).1 (X t) (V t)
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hpde
    exact hpde ▸ hder
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope (fun r => s.f (r,X r,V r)) (fun _ => 0) h hc hd
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h)))

lemma continuousOn_lorentz_along {E B : Field} {α : ℝ → Phase} {T : ℝ}
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) :
    ContinuousOn (fun r => lorentzField E B (r,α r)) (Icc (0:ℝ) T) := by
  have hx : ContinuousOn (fun r => (r,(α r).1)) (Icc (0:ℝ) T) := continuousOn_id.prodMk hα.fst
  have hm : MapsTo (fun r => (r,(α r).1)) (Icc (0:ℝ) T) fieldHalfSpace := fun r hr => hr.1
  have hu : ContinuousOn (fun r => velocity (α r).2) (Icc (0:ℝ) T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hα.snd
  exact hu.prodMk ((hE.continuousOn.comp hx hm).add
    ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk (hB.continuousOn.comp hx hm))))

lemma admissible_particle_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ A : ℝ, 0≤A ∧ ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖ := by
  obtain ⟨A,hA⟩ := (hd.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hd.2.1.fderiv ℝ)
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro z w
  have hh := (convex_univ : Convex ℝ (univ : Set Phase)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd.1.differentiable (by simp) z) (C:=max A 0)
    (fun z _ => (hA z).trans (le_max_left A 0)) (mem_univ w) (mem_univ z)
  simpa only [Real.norm_eq_abs] using hh

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_ode_inhomogeneous_bound {z dz : ℝ → E} {c : ℝ → ℝ} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hc : ContinuousOn c (Icc (0:ℝ) T)) (hc0 : ∀ r∈Icc (0:ℝ) T,0 ≤ c r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖+c r) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤(‖z 0‖+∫ r in 0..T,c r)*Real.exp (K*t) := by
  have hb : ∀ t∈Icc (0:ℝ) T,‖z t‖≤(‖z 0‖+∫ r in 0..T,c r)+∫ r in 0..t,K*‖z r‖ := by
    intro t ht
    have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
    have hi : IntervalIntegrable dz volume 0 t := (hdz.mono hsub).intervalIntegrable_of_Icc ht.1
    have he : ∫ r in 0..t,dz r=z t-z 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hz.mono hsub)
        (fun r hr => hder r ⟨hr.1,hr.2.trans_le ht.2⟩) hi
    have hci : IntervalIntegrable c volume 0 t := (hc.mono hsub).intervalIntegrable_of_Icc ht.1
    have hki : IntervalIntegrable (fun r => K*‖z r‖) volume 0 t := ((continuousOn_const.mul hz.norm).mono hsub).intervalIntegrable_of_Icc ht.1
    have hcle : (∫ r in 0..t,c r)≤∫ r in 0..T,c r := by
      apply intervalIntegral.integral_mono_interval (μ:=volume) le_rfl ht.1 ht.2 _
        (hc.intervalIntegrable_of_Icc hT)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hc0 r ⟨hr.1.le,hr.2⟩
    calc
      ‖z t‖ = ‖z 0+∫ r in 0..t,dz r‖ := by rw [he]; congr 1; abel
      _ ≤ ‖z 0‖+∫ r in 0..t,‖dz r‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm ht.1))
      _ ≤ ‖z 0‖+∫ r in 0..t,K*‖z r‖+c r := by
        apply add_le_add le_rfl
        exact intervalIntegral.integral_mono_on ht.1 hi.norm (hki.add hci) (fun r hr => hbound r (hsub hr))
      _ ≤ _ := by rw [intervalIntegral.integral_add hki hci]; linarith
  have hh := variable_integral_gronwall_bound_on hT hz.norm continuousOn_const (fun _ _ => hK) hb
  intro t ht
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm t K] using hh t ht

lemma backward_norm_ode_uniform_bound {z dz : ℝ → E} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖) :
    ∀ t∈Icc (0:ℝ) T,‖z t‖≤‖z T‖*Real.exp (K*T) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_volterra_bound hT (hz.comp hc.continuousOn hm)
    (hdz.neg.comp hc.continuousOn hm) continuousOn_const (fun _ _ => hK) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr))
  intro t ht
  have h := hh (T-t) (hm ht)
  simp only [Function.comp_apply,sub_zero,sub_sub_cancel,intervalIntegral.integral_const,smul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.1])) (norm_nonneg _))

lemma backward_norm_ode_inhomogeneous_bound {z dz : ℝ → E} {c : ℝ → ℝ} {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hc : ContinuousOn c (Icc (0:ℝ) T)) (hc0 : ∀ r∈Icc (0:ℝ) T,0 ≤ c r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤K*‖z r‖+c r) :
    ‖z 0‖≤(‖z T‖+∫ r in 0..T,c r)*Real.exp (K*T) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc' : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_inhomogeneous_bound hT hK (hz.comp hc'.continuousOn hm)
    (hdz.neg.comp hc'.continuousOn hm) (hc.comp hc'.continuousOn hm)
    (fun r hr => hc0 (T-r) (hm hr)) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr)) T ⟨hT,le_rfl⟩
  simpa only [Function.comp_apply,sub_self,sub_zero,intervalIntegral.integral_comp_sub_left] using hh

end

lemma exists_phase_characteristic_before {d : Datum} {s : Solution} {T U : ℝ}
    (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U) (z : Phase) :
    ∃ α : ℝ → Phase, α T=z ∧ ContinuousOn α (Icc (0:ℝ) T) ∧
      (∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField s.E s.B (r,α r)) r) ∧
      s.f (T,z)=d.f₀ (α 0) := by
  obtain ⟨X,V,hXT,hVT,hX,hV,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 z.1 z.2
  have hXc : ContinuousOn X (Icc 0 T) := fun r hr => (hX r hr).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun r hr => (hV r hr).continuousWithinAt
  have hdX := fun r hr => (hX r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdV := fun r hr => (hV r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hf := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hXc hVc hdX hdV
  rw [hXT,hVT,hs.2.2.2.2.2.2.2.2.1] at hf
  exact ⟨fun r => (X r,V r),by simp [hXT,hVT],hXc.prodMk hVc,
    fun r hr => (hdX r hr).prodMk (hdV r hr),hf⟩

lemma characteristic_separation_uniform {E B : Field} {α γ : ℝ → Phase} {T L N : ℝ}
    (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤N*‖y-x‖) :
    ∀ r∈Icc (0:ℝ) T,‖α r-γ r‖≤‖α T-γ T‖*Real.exp ((1+2*N+L)*T) := by
  apply backward_norm_ode_uniform_bound hT (by positivity : 0≤1+2*N+L) (hα.sub hγ)
    ((continuousOn_lorentz_along hE hB hα).sub (continuousOn_lorentz_along hE hB hγ))
    (fun r hr => (hdα r hr).sub (hdγ r hr))
  intro r hr
  exact (lorentzField_difference_bound hL hN (D:=0) le_rfl (hBb r hr) (hEx r hr) (hBx r hr)
    (by intros; simp) (by intros; simp) (α r) (γ r)).trans_eq (by simp)

lemma characteristic_curvature_volterra {E B : Field} {α β γ : ℝ → Phase}
    {T L N : ℝ} {g : ℝ → ℝ} {z v : Phase}
    (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hβ : ContinuousOn β (Icc (0:ℝ) T))
    (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdβ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt β (lorentzField E B (r,β r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hαT : α T=z+v) (hβT : β T=z-v) (hγT : γ T=z)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤N*‖y-x‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hEc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => E (r,x)) (g r))
    (hBc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => B (r,x)) (g r)) :
    ‖α 0+β 0-(2:ℝ) • γ 0‖≤
      (4*(Real.exp ((1+2*N+L)*T))^3*(∫ r in 0..T,6+6*L+2*g r+2*N))*‖v‖^2 := by
  let K := 1+2*N+L
  let Q := Real.exp (K*T)
  let C := fun r => 6+6*L+2*g r+2*N
  let δ := fun r => α r+β r-(2:ℝ) • γ r
  let dδ := fun r => lorentzField E B (r,α r)+lorentzField E B (r,β r)-
    (2:ℝ) • lorentzField E B (r,γ r)
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ : 0<Q := Real.exp_pos _
  have hC : ∀ r∈Icc (0:ℝ) T,0≤C r := by intro r hr; dsimp [C]; have := hg0 r hr; positivity
  have hdc : ContinuousOn δ (Icc (0:ℝ) T) := (hα.add hβ).sub (hγ.const_smul (2:ℝ))
  have hddc : ContinuousOn dδ (Icc (0:ℝ) T) :=
    ((continuousOn_lorentz_along hE hB hα).add (continuousOn_lorentz_along hE hB hβ)).sub
      ((continuousOn_lorentz_along hE hB hγ).const_smul (2:ℝ))
  have hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt δ (dδ r) r :=
    fun r hr => ((hdα r hr).add (hdβ r hr)).sub ((hdγ r hr).const_smul (2:ℝ))
  have hsep := characteristic_separation_uniform hT hL hN hE hB hα hβ hdα hdβ hBb hEx hBx
  have hdT : δ T=0 := by dsimp [δ]; rw [hαT,hβT,hγT]; module
  have hb : ∀ r∈Icc (0:ℝ) T,‖dδ r‖≤K*‖δ r‖+(4*Q^2*‖v‖^2)*C r := by
    intro r hr
    have hf := lorentzField_curvature hL hN (hg0 r hr) (hBb r hr) (hBx r hr) (hEc r hr) (hBc r hr)
    have hfl (a b : Phase) : ‖lorentzField E B (r,b)-lorentzField E B (r,a)‖≤K*‖b-a‖ := by
      simpa only [mul_zero,add_zero] using lorentzField_difference_bound hL hN (D:=0) le_rfl
        (hBb r hr) (hEx r hr) (hBx r hr) (by intros; simp) (by intros; simp) b a
    have htr := hf.triple (hC r hr) hK hfl (α r) (β r) (γ r)
    have hs := hsep r hr
    rw [hαT,hβT,show z+v-(z-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hs
    norm_num at hs
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖v‖*Q)).mpr hs
    have hh := mul_le_mul_of_nonneg_left hsq (hC r hr)
    change ‖_‖≤K*‖α r+β r-(2:ℝ) • γ r‖+_
    nlinarith [htr,hh]
  have hc : ContinuousOn (fun r => (4*Q^2*‖v‖^2)*C r) (Icc (0:ℝ) T) := by dsimp [C]; fun_prop
  have hh := backward_norm_ode_inhomogeneous_bound hT hK hdc hddc hc
    (fun r hr => mul_nonneg (by positivity) (hC r hr)) hder hb
  rw [hdT,norm_zero,zero_add,intervalIntegral.integral_const_mul] at hh
  exact hh.trans_eq (by dsimp [δ,Q,K,C]; ring)

lemma particle_curvature_volterra_before {d : Datum} {s : Solution} {T U A D L N : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hD : 0≤D) (hL : 0≤L) (hN : 0≤N)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖) (hc₀ : CurvatureBound d.f₀ D)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤N*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤N*‖y-x‖)
    (hEc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => s.E (r,x)) (g r))
    (hBc : ∀ r∈Icc (0:ℝ) T,CurvatureBound (fun x => s.B (r,x)) (g r)) :
    CurvatureBound (fun z => s.f (T,z))
      (4*D*(Real.exp ((1+2*N+L)*T))^2+
        A*4*(Real.exp ((1+2*N+L)*T))^3*(∫ r in 0..T,6+6*L+2*g r+2*N)) := by
  intro z v
  obtain ⟨α,hαT,hα,hdα,hfα⟩ := exists_phase_characteristic_before hs hT hTU (z+v)
  obtain ⟨β,hβT,hβ,hdβ,hfβ⟩ := exists_phase_characteristic_before hs hT hTU (z-v)
  obtain ⟨γ,hγT,hγ,hdγ,hfγ⟩ := exists_phase_characteristic_before hs hT hTU z
  have hfL (a b : Phase) : ‖d.f₀ b-d.f₀ a‖≤A*‖b-a‖ := h₀ b a
  have ht := hc₀.triple hD hA hfL (α 0) (β 0) (γ 0)
  have hc := characteristic_curvature_volterra hT hL hN hs.2.1 hs.2.2.1 hα hβ hγ
    hdα hdβ hdγ hαT hβT hγT hBb hEx hBx hg hg0 hEc hBc
  have hsep := characteristic_separation_uniform hT hL hN hs.2.1 hs.2.2.1 hα hβ
    hdα hdβ hBb hEx hBx 0 ⟨le_rfl,hT⟩
  rw [hαT,hβT,show z+v-(z-v)=(2:ℝ) • v by module,norm_smul,Real.norm_eq_abs] at hsep
  norm_num at hsep
  have hp := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsep
  have hd := mul_le_mul_of_nonneg_left hp hD
  have ha := mul_le_mul_of_nonneg_left hc hA
  simp only [hfα,hfβ,hfγ]
  nlinarith [ht,hd,ha]


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma CurvatureBound.fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) :
    ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤6*H*‖y-x‖ := by
  have htaylor (basePoint increment : U) :
      ‖f (basePoint+increment)-f basePoint-fderiv ℝ f basePoint increment‖≤H*‖increment‖^2 := by
    let dyadicSequence : ℕ → W := fun index =>
      (2:ℝ)^index • (f (basePoint+(1/2:ℝ)^index • increment)-f basePoint)
    have hderivative : HasDerivAt (fun time : ℝ => f (basePoint+time • increment))
        (fderiv ℝ f basePoint increment) 0 := by
      have hcomposition := (hf (basePoint+(0:ℝ) • increment)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
        ((hasDerivAt_const (0:ℝ) basePoint).add ((hasDerivAt_id (0:ℝ)).smul_const increment))
      simpa only [zero_smul,add_zero,one_smul,zero_add,Function.comp_def,Pi.add_apply,id_eq] using hcomposition
    have hpowers : Tendsto (fun index : ℕ => (1/2:ℝ)^index) atTop (𝓝[>] (0:ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
        Eventually.of_forall (fun index => by simp only [mem_Ioi]; positivity)⟩
    have hlimit : Tendsto dyadicSequence atTop (𝓝 (fderiv ℝ f basePoint increment)) := by
      simpa [Function.comp_def,dyadicSequence,← inv_pow] using hderivative.tendsto_slope_zero_right.comp hpowers
    have hstep (index : ℕ) : dist (dyadicSequence index) (dyadicSequence (index+1))≤
        (H*‖increment‖^2/2)*(1/2:ℝ)^index := by
      let scale : ℝ := (1/2:ℝ)^index
      have hscale : 0 ≤ scale := by dsimp [scale]; positivity
      have hpower : 0≤(2:ℝ)^index := by positivity
      have hinverse : (2:ℝ)^index*scale=1 := by dsimp [scale]; rw [← mul_pow]; norm_num
      have hcenter := hc (basePoint+(scale/2) • increment) ((scale/2) • increment)
      rw [show (basePoint+(scale/2) • increment)+(scale/2) • increment=basePoint+scale • increment by module,
        show (basePoint+(scale/2) • increment)-(scale/2) • increment=basePoint by module,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ scale/2)] at hcenter
      have hdifference : dyadicSequence index-dyadicSequence (index+1)=
          (2:ℝ)^index • (f (basePoint+scale • increment)+f basePoint-
            (2:ℝ) • f (basePoint+(scale/2) • increment)) := by
        dsimp only [dyadicSequence]
        rw [pow_succ,pow_succ]
        change (2:ℝ)^index • (f (basePoint+scale • increment)-f basePoint)-
          ((2:ℝ)^index*2) • (f (basePoint+(scale*(1/2)) • increment)-f basePoint)=_
        rw [show scale*(1/2)=scale/2 by ring]
        module
      rw [dist_eq_norm,hdifference,norm_smul,Real.norm_eq_abs,abs_of_nonneg hpower]
      apply (mul_le_mul_of_nonneg_left hcenter hpower).trans
      have hequality : (2:ℝ)^index*(H*(scale/2*‖increment‖)^2)=(H*‖increment‖^2/4)*scale := by
        calc
          _ = (H*‖increment‖^2/4)*((2:ℝ)^index*scale)*scale := by ring
          _ = _ := by rw [hinverse]; ring
      rw [hequality]
      change (H*‖increment‖^2/4)*scale≤(H*‖increment‖^2/2)*scale
      gcongr
      nlinarith [mul_nonneg hH (sq_nonneg ‖increment‖)]
    have hgeometric := dist_le_of_le_geometric_of_tendsto₀
      (r:=(1/2:ℝ)) (C:=H*‖increment‖^2/2) (by norm_num) hstep hlimit
    simpa only [dyadicSequence,pow_zero,one_smul,dist_eq_norm,
      show (H*‖increment‖^2/2)/(1-(1/2:ℝ))=H*‖increment‖^2 by ring] using hgeometric
  intro x y
  by_cases he : y=x
  · subst y; simp
  have hr : 0<‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let r := ‖y-x‖
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let w := r • v
  have hw : ‖w‖=r := by dsimp [w]; rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one]
  have h1 := htaylor x (y+w-x)
  have h2 := htaylor x (y-x)
  have h3 := htaylor y w
  rw [show x+(y+w-x)=y+w by abel] at h1
  rw [show x+(y-x)=y by abel] at h2
  let R1 := f (y+w)-f x-fderiv ℝ f x (y+w-x)
  let R2 := f y-f x-fderiv ℝ f x (y-x)
  let R3 := f (y+w)-f y-fderiv ℝ f y w
  have hid : (fderiv ℝ f y-fderiv ℝ f x) w=R1-R2-R3 := by
    dsimp [R1,R2,R3]
    simp only [sub_apply,map_sub,map_add]
    abel
  have hnorm : ‖y+w-x‖≤2*r := by
    rw [show y+w-x=(y-x)+w by abel]
    exact (norm_add_le _ _).trans (by rw [hw]; change r+r≤2*r; linarith)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*r)).mpr hnorm
  have hb : ‖(fderiv ℝ f y-fderiv ℝ f x) w‖≤6*H*r^2 := by
    rw [hid]
    have h := (norm_sub_le (R1-R2) R3).trans (add_le_add (norm_sub_le R1 R2) (le_refl ‖R3‖))
    rw [hw] at h3
    have hp := mul_le_mul_of_nonneg_left hsq hH
    nlinarith [h,h1,h2,h3,hp]
  rw [show (fderiv ℝ f y-fderiv ℝ f x) w=r • ((fderiv ℝ f y-fderiv ℝ f x) v) by
    exact map_smul _ _ _,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hb
  change ‖(fderiv ℝ f y-fderiv ℝ f x) v‖≤6*H*r
  nlinarith

lemma CurvatureBound.second_derivative_bound {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (x : U) : ‖iteratedFDeriv ℝ 2 f x‖≤6*H := by
  have hL : LipschitzWith ⟨6*H,by positivity⟩ (fderiv ℝ f) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    change dist (fderiv ℝ f y) (fderiv ℝ f z)≤(6*H)*dist y z
    simpa only [dist_eq_norm] using hc.fderiv_lipschitz hH hf z y
  have hh := norm_fderiv_le_of_lipschitz ℝ hL (x₀:=x)
  change ‖fderiv ℝ (fderiv ℝ f) x‖≤6*H at hh
  simpa only [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv] using hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_UpperTimeCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_upperTimeCut (τ H : ℝ) : ContDiff ℝ ∞ (upperTimeCut τ H) :=
  (contDiff_positiveTimeCut _).comp (contDiff_const.sub contDiff_id)

lemma upperTimeCut_nonneg (τ H t : ℝ) : 0 ≤ upperTimeCut τ H t :=
  Real.smoothTransition.nonneg _

lemma upperTimeCut_one {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ) :
    upperTimeCut τ H t = 1 := by
  apply positiveTimeCut_one (by linarith)
  linarith

lemma upperTimeCut_zero {τ H t : ℝ} (hτ : τ < H) (ht : (τ+H)/2 ≤ t) :
    upperTimeCut τ H t = 0 := by
  apply positiveTimeCut_zero (by linarith)
  linarith

section Generic
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma upperTimeExtend_eq {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ)
    (F : ℝ × X → W) (x : X) : upperTimeExtend τ H F (t,x)=F (t,x) := by
  simp only [upperTimeExtend,upperTimeCut_one hτ ht,one_smul]

omit [NormedSpace ℝ X] in
lemma upperTimeExtend_eventually_zero {τ H : ℝ} (hτ : τ < H)
    (F : ℝ × X → W) {p : ℝ × X} (hp : (τ+H)/2 < p.1) :
    upperTimeExtend τ H F =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [upperTimeExtend,upperTimeCut_zero hτ hq.le,zero_smul]

lemma contDiffOn_upperTimeExtend {τ H : ℝ} (hτ : τ < H) {F : ℝ × X → W}
    (hF : ContDiffOn ℝ ∞ F {p | p.1 ∈ Icc 0 H}) :
    ContDiffOn ℝ ∞ (upperTimeExtend τ H F) {p | 0 ≤ p.1} := by
  intro p hp
  by_cases hpt : p.1 < H
  · have hlocal : {q : ℝ × X | q.1 ∈ Icc 0 H} ∈ 𝓝[{q | 0 ≤ q.1}] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_fst continuous_const).mem_nhds hpt),
        self_mem_nhdsWithin] with q hq hq0
      exact ⟨hq0,hq.le⟩
    exact (((contDiff_upperTimeCut τ H).comp contDiff_fst).contDiffAt.contDiffWithinAt).smul
      ((hF p ⟨hp,hpt.le⟩).mono_of_mem_nhdsWithin hlocal)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (upperTimeExtend_eventually_zero hτ F (show (τ+H)/2 < p.1 by linarith))).contDiffWithinAt

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma derivWithin_upperTimeExtend {τ H t : ℝ} (hτ : τ < H) (ht : t < τ)
    (F : ℝ × X → W) (x : X) (S : Set ℝ) :
    derivWithin (fun r => upperTimeExtend τ H F (r,x)) S t =
      derivWithin (fun r => F (r,x)) S t := by
  have he : (fun r => upperTimeExtend τ H F (r,x)) =ᶠ[𝓝 t] (fun r => F (r,x)) := by
    filter_upwards [Iio_mem_nhds ht] with r hr
    exact upperTimeExtend_eq hτ hr.le F x
  exact he.filter_mono nhdsWithin_le_nhds |>.derivWithin_eq (upperTimeExtend_eq hτ ht.le F x)
end Generic

lemma timeContinuousL2_upperTimeExtend {τ H : ℝ} (hτ : τ < H) (hH : 0 ≤ H)
    {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn F₂ (Icc 0 H) ∧ ∀ t ∈ Icc 0 H,
        (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 (upperTimeExtend τ H F) := by
  obtain ⟨F₂,hc,he⟩ := hF
  refine ⟨fun t => upperTimeCut τ H t • F₂ (min t H),?_,?_⟩
  · exact (contDiff_upperTimeCut τ H).continuous.continuousOn.smul
      (hc.comp (continuous_id.min continuous_const).continuousOn
        (fun t ht => ⟨le_min ht hH,min_le_right _ _⟩))
  · intro t ht
    have hl := Lp.coeFn_smul (upperTimeCut τ H t) (F₂ (min t H))
    by_cases htH : t ≤ H
    · rw [min_eq_left htH] at hl
      filter_upwards [hl,he t ⟨ht,htH⟩] with x hx hx'
      simpa only [min_eq_left htH,upperTimeExtend,Pi.smul_apply,hx'] using hx
    · have hz := upperTimeCut_zero hτ (show (τ+H)/2 ≤ t by linarith)
      filter_upwards [hl] with x hx
      simpa only [hz,upperTimeExtend,zero_smul,Pi.zero_apply,Pi.smul_apply] using hx

lemma cutoffPrefix_eq {τ H t : ℝ} (hτH : τ < H) (ht : t ≤ τ) (s : Solution) :
    (∀ z, (cutoffPrefix τ H s).f (t,z)=s.f (t,z)) ∧
    (∀ x, (cutoffPrefix τ H s).E (t,x)=s.E (t,x)) ∧
    (∀ x, (cutoffPrefix τ H s).B (t,x)=s.B (t,x)) :=
  ⟨upperTimeExtend_eq hτH ht s.f,upperTimeExtend_eq hτH ht s.E,
    upperTimeExtend_eq hτH ht s.B⟩

lemma cutoffPrefix_equations {s : Solution} {τ H : ℝ} (hτH : τ < H)
    (hs : EquationsBefore s H) : EquationsBefore (cutoffPrefix τ H s) τ := by
  intro t ht htτ
  have hh := hs t ht (htτ.trans hτH)
  have hf (x v : Vec) := derivWithin_upperTimeExtend hτH htτ s.f (x,v) (Ici 0)
  have hE (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.E x (Ici 0)
  have hB (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.B x (Ici 0)
  change (∀ x v, derivWithin (fun r => upperTimeExtend τ H s.f (r,x,v)) (Ici 0) t + _ + _ = 0) ∧ _
  simp only [cutoffPrefix]
  simp only [hf,hE,hB]
  simpa only [upperTimeExtend,upperTimeCut_one hτH htτ.le,one_smul] using hh

lemma SmoothClassicalPrefix.cutoff_smooth {d : Datum} {s : Solution} {τ H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hτH : τ < H) :
    SmoothOnFiniteHorizons (cutoffPrefix τ H s) := by
  intro T _hT
  exact ⟨(contDiffOn_upperTimeExtend hτH hs.f_smooth).mono (fun _ hp => hp.1),
    (contDiffOn_upperTimeExtend hτH hs.E_smooth).mono (fun _ hp => hp.1),
    (contDiffOn_upperTimeExtend hτH hs.B_smooth).mono (fun _ hp => hp.1)⟩

lemma SmoothClassicalPrefix.cutoff_classical_before {d : Datum} {s : Solution} {τ H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hτ : 0 ≤ τ) (hτH : τ < H) :
    ClassicalBefore d (cutoffPrefix τ H s) τ := by
  have hH : 0 ≤ H := hτ.trans hτH.le
  refine ⟨(contDiffOn_upperTimeExtend hτH hs.f_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.E_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.B_smooth).of_le (by decide),?_,
    timeContinuousL2_upperTimeExtend hτH hH hs.E_L2,
    timeContinuousL2_upperTimeExtend hτH hH hs.B_L2,?_,
    cutoffPrefix_equations hτH hs.equations,?_,?_,?_⟩
  · intro t ht z
    by_cases htH : t ≤ H
    · exact mul_nonneg (upperTimeCut_nonneg τ H t) (hs.nonnegative t ⟨ht,htH⟩ z)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul,le_refl]
  · obtain ⟨K,hK,hk⟩ := hs.compact
    intro T _hT
    refine ⟨K,hK,?_⟩
    intro t ht
    by_cases htH : t ≤ H
    · exact (tsupport_smul_subset_right (fun _ : Phase => upperTimeCut τ H t)
        (fun z => s.f (t,z))).trans (hk t ⟨ht.1,htH⟩)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul]
      change tsupport (0 : Phase → ℝ) ⊆ K
      simp only [tsupport_zero,empty_subset]
  · intro z
    exact (cutoffPrefix_eq hτH hτ s).1 z |>.trans (hs.initial_f z)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.1 x |>.trans (hs.initial_E x)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.2 x |>.trans (hs.initial_B x)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_GlobalContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma secondJetSum_nonneg (s : Solution) (t : ℝ) (z : Phase) : 0 ≤ secondJetSum s t z := by
  dsimp [secondJetSum]; positivity

lemma prefix_second_jet_volterra_oai {d : Datum} (hd : Admissible d)
    (P A L M N H : ℝ) (hL : 0≤L) (hM : 0≤M) (hN : 0≤N) (hH : 0≤H) :
    ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U : ℝ),
      BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U,∀ y v,|s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U,∀ y v,P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U,∀ y,‖s.E (u,y)‖≤L ∧ ‖s.B (u,y)‖≤L) →
      (∀ u∈Icc (0:ℝ) U,∀ z w : Phase,|s.f (u,z)-s.f (u,w)|≤M*‖z-w‖) →
      SpatialFieldLip U N s.E s.B →
      ∀ g : ℝ → ℝ,Continuous g →
      (∀ u∈Icc (0:ℝ) U,∀ z,secondJetSum s u z≤g u) →
      ∀ t∈Icc (0:ℝ) U,∀ z,secondJetSum s t z≤D+K*(∫ r in Icc (0:ℝ) t,1+g r) := by
  obtain ⟨D,K,hD,hK,hfield⟩ := classical_fields_curvature_volterra_bound hd A P L M N H hM hN hH
  obtain ⟨Af,hAf,hfl⟩ := admissible_particle_lipschitz hd
  obtain ⟨Df,hDf,hfc⟩ := smooth_compact_curvature hd.1 hd.2.1
  let Q := Real.exp ((1+2*N+L)*H)
  let Bf := 4*Df*Q^2
  let Kf := Af*4*Q^3*(10+6*L+2*N)
  have hQ : 0<Q := Real.exp_pos _
  have hBf : 0≤Bf := by dsimp [Bf]; positivity
  have hKf : 0≤Kf := by dsimp [Kf]; positivity
  refine ⟨6*Bf+12*D,6*Kf+24*K,by positivity,by positivity,?_⟩
  intro s U hs hU hUH hfA hP hEB hfL hEBL g hg hgb
  have hg0 : ∀ u∈Icc (0:ℝ) U,0≤g u := fun u hu => (secondJetSum_nonneg s u 0).trans (hgb u hu 0)
  have hf2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (z : Phase) :
      ‖iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) z‖≤g u := by
    have hh := hgb u hu z
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) z.1),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) z.1)]
  have hE2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (x : Vec) :
      ‖iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) x‖≤g u := by
    have hh := hgb u hu (x,0)
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) x)]
  have hB2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (x : Vec) :
      ‖iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) x‖≤g u := by
    have hh := hgb u hu (x,0)
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) x)]
  have hinterior : ∀ t∈Ioo (0:ℝ) U,∀ z,
      secondJetSum s t z≤(6*Bf+12*D)+(6*Kf+24*K)*(∫ r in Icc (0:ℝ) t,1+g r) := by
    intro t ht z
    obtain ⟨τ,htτ,hτU⟩ := exists_between ht.2
    let a := cutoffPrefix τ U s
    have heq (u : ℝ) (hu : u≤τ) := cutoffPrefix_eq hτU hu s
    have ha := hs.classical.cutoff_classical_before (ht.1.le.trans htτ.le) hτU
    have hsub : Icc (0:ℝ) τ ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans hτU.le⟩
    have hsf (u : ℝ) (hu : u≤τ) : (fun w : Phase => a.f (u,w))=(fun w => s.f (u,w)) :=
      funext (fun w => (heq u hu).1 w)
    have hsE (u : ℝ) (hu : u≤τ) : (fun y => a.E (u,y))=(fun y => s.E (u,y)) := funext (heq u hu).2.1
    have hsB (u : ℝ) (hu : u≤τ) : (fun y => a.B (u,y))=(fun y => s.B (u,y)) := funext (heq u hu).2.2
    have hafc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun w : Phase => a.f (u,w)) (2*g u) := by
      intro u hu
      rw [hsf u hu.2]
      exact curvature_of_second_derivative_bound (hs.f_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hf2 u (hsub hu))
    have haEc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun y => a.E (u,y)) (2*g u) := by
      intro u hu
      rw [hsE u hu.2]
      exact curvature_of_second_derivative_bound (hs.E_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hE2 u (hsub hu))
    have haBc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun y => a.B (u,y)) (2*g u) := by
      intro u hu
      rw [hsB u hu.2]
      exact curvature_of_second_derivative_bound (hs.B_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hB2 u (hsub hu))
    have haEB : ∀ u∈Icc (0:ℝ) τ,∀ y,‖a.E (u,y)‖≤L ∧ ‖a.B (u,y)‖≤L := by
      intro u hu y
      simp only [a,(heq u hu.2).2.1,(heq u hu.2).2.2]
      exact hEB u (hsub hu) y
    have haL : SpatialFieldLip τ N a.E a.B := by
      intro u hu x y
      simp only [a,(heq u hu.2).2.1,(heq u hu.2).2.2]
      exact hEBL u (hsub hu) x y
    have haA : ∀ u∈Icc (0:ℝ) τ,∀ y v,|a.f (u,y,v)|≤A := by
      intro u hu y v
      rw [(heq u hu.2).1]
      exact hfA u (hsub hu) y v
    have haP : ∀ u∈Icc (0:ℝ) τ,∀ y v,P<‖v‖ → a.f (u,y,v)=0 := by
      intro u hu y v hv
      rw [(heq u hu.2).1]
      exact hP u (hsub hu) y v hv
    have haLf : ∀ u∈Icc (0:ℝ) τ,∀ v x y,|a.f (u,y,v)-a.f (u,x,v)|≤M*‖y-x‖ := by
      intro u hu v x y
      simp only [a,(heq u hu.2).1]
      have hh := hfL u (hsub hu) (y,v) (x,v)
      simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_left (norm_nonneg (y-x))] using hh
    have hg2 : Continuous (fun u => 2*g u) := continuous_const.mul hg
    have hg20 : ∀ u∈Icc (0:ℝ) τ,0≤2*g u := fun u hu => by positivity [hg0 u (hsub hu)]
    have hfields := hfield a τ t (fun u => 2*g u) ha (hs.classical.cutoff_smooth hτU) ht.1 htτ
      (hτU.le.trans hUH) hg2 hg20 haA haP haEB
      (fun u hu v => (hafc u hu).spatial_slice v) (fun u hu => ⟨haEc u hu,haBc u hu⟩) haLf haL
    rw [hsE t htτ.le,hsB t htτ.le] at hfields
    have hsubt : Icc (0:ℝ) t ⊆ Icc (0:ℝ) τ := fun u hu => ⟨hu.1,hu.2.trans htτ.le⟩
    have hpart := particle_curvature_volterra_before ha ht.1.le htτ.le hAf hDf hL hN hfl hfc
      (hg2.continuousOn) (fun u hu => hg20 u (hsubt hu))
      (fun u hu y => (haEB u (hsubt hu) y).2)
      (fun u hu x y => (haL u (hsubt hu) x y).1) (fun u hu x y => (haL u (hsubt hu) x y).2)
      (fun u hu => haEc u (hsubt hu)) (fun u hu => haBc u (hsubt hu))
    rw [hsf t htτ.le] at hpart
    let I := ∫ r in Icc (0:ℝ) t,1+g r
    have hI : 0≤I := integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
      change 0≤1+g r; linarith)
    have hInt2 : (∫ r in Icc (0:ℝ) t,1+2*g r)≤2*I := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc (fun r hr => by linarith)
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    have hIntP : (∫ r in 0..t,6+6*L+2*(2*g r)+2*N)≤(10+6*L+2*N)*I := by
      rw [intervalIntegral.integral_of_le ht.1.le,←integral_Icc_eq_integral_Ioc,←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc
      · intro r hr
        have hg' := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
        change 6+6*L+2*(2*g r)+2*N≤(10+6*L+2*N)*(1+g r)
        nlinarith [mul_nonneg hL hg',mul_nonneg hN hg']
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    have hQt : Real.exp ((1+2*N+L)*t)≤Q := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (ht.2.le.trans hUH) (by positivity))
    have hpart' : CurvatureBound (fun w => s.f (t,w)) (Bf+Kf*I) := by
      apply hpart.mono
      have h0 : 0≤∫ r in 0..t,6+6*L+2*(2*g r)+2*N := by
        apply intervalIntegral.integral_nonneg ht.1.le
        intro r hr
        have := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
        positivity
      dsimp [Bf,Kf]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hQt 2) (by positivity)
      · exact (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hQt 3)
          (by positivity)) hIntP h0 (by positivity)).trans_eq (by ring)
    have hfields' : CurvatureBound (fun y => s.E (t,y)) (D+K*(2*I)) ∧
        CurvatureBound (fun y => s.B (t,y)) (D+K*(2*I)) := ⟨hfields.1.mono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hInt2 hK)),
      hfields.2.mono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hInt2 hK))⟩
    have hp := hpart'.second_derivative_bound (by positivity) ((hs.f_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z
    have he := hfields'.1.second_derivative_bound (by positivity) ((hs.E_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z.1
    have hb := hfields'.2.second_derivative_bound (by positivity) ((hs.B_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z.1
    dsimp [secondJetSum]
    nlinarith
  intro t ht z
  have hcont : ContinuousOn (fun r => secondJetSum s r z) (Icc (0:ℝ) U) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact (((hs.f_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
      · exact (((hs.E_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
    · exact (((hs.B_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
  have hgc : ContinuousOn (fun r => (6*Bf+12*D)+(6*Kf+24*K)*(∫ u in Icc (0:ℝ) r,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure (fun r hr => hinterior r hr z)
  · simpa only [_root_.closure_Ioo hU.ne] using hcont
  · simpa only [_root_.closure_Ioo hU.ne] using hgc
  · simpa only [_root_.closure_Ioo hU.ne] using ht

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.prefix_second_jet_volterra_oai := @OAI.RVM.prefix_second_jet_volterra_oai
