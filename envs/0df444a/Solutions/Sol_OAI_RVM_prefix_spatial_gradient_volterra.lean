-- Prove2me | solution 1 for OAI.RVM.prefix_spatial_gradient_volterra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:42:45.626591+00:00
-- url     : https://prove2.me/submissions/b948d0a4-3ff0-458e-9f97-7803bfd5f7bc

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Magnetic_classical_magnetic_gradient_volterra_bound
import Theorems.Thm_OAI_RVM_classical_electric_log_closed_bound

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma field_differentiableAt_positive {F : Field}
    (hF : ContDiffOn ℝ 1 F fieldHalfSpace) {t : ℝ} (ht : 0 < t) (x : Vec) :
    DifferentiableAt ℝ F (t,x) := by
  apply (hF.contDiffAt _).differentiableAt (by simp)
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  intro z hz
  change 0 ≤ z.1
  exact le_of_lt hz

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

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

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_BranchIntegral
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma norm_coordinate_le (v : Vec) (i : Fin 3) : |v i|≤‖v‖ := by
  exact (PiLp.norm_apply_le v i)

lemma norm_le_three_of_coordinate_bound {v : Vec} {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, |v i|≤C) : ‖v‖≤3*C := by
  have hsq (i : Fin 3) : (v i)^2≤C^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using h i)
  have hnorm := dot_self v
  simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hnorm
  change v 0*v 0+(v 1*v 1+v 2*v 2)=‖v‖^2 at hnorm
  nlinarith [hsq 0,hsq 1,hsq 2,norm_nonneg v]

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

lemma coordinate_fderiv_apply {F : Vec → Vec} (hF : Differentiable ℝ F)
    (x v : Vec) (i : Fin 3) : fderiv ℝ (fun y => F y i) x v = (fderiv ℝ F x v) i := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L v)
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv)

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

lemma backward_norm_ode_volterra_bound {z dz : ℝ → E} {b : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hz : ContinuousOn z (Icc (0:ℝ) T)) (hdz : ContinuousOn dz (Icc (0:ℝ) T))
    (hb : ContinuousOn b (Icc (0:ℝ) T)) (hb0 : ∀ r∈Icc (0:ℝ) T,0≤b r)
    (hder : ∀ r∈Ioo (0:ℝ) T,HasDerivAt z (dz r) r)
    (hbound : ∀ r∈Icc (0:ℝ) T,‖dz r‖≤b r*‖z r‖) :
    ‖z 0‖≤‖z T‖*Real.exp (∫ r in 0..T,b r) := by
  have hm : MapsTo (fun r:ℝ => T-r) (Icc (0:ℝ) T) (Icc (0:ℝ) T) :=
    fun r hr => ⟨sub_nonneg.mpr hr.2,sub_le_self _ hr.1⟩
  have hc : Continuous (fun r:ℝ => T-r) := continuous_const.sub continuous_id
  have he (r : ℝ) (hr : r∈Ioo (0:ℝ) T) :
      HasDerivAt (fun u => z (T-u)) (-dz (T-r)) r := by
    have hd := (hder (T-r) ⟨by linarith [hr.2],by linarith [hr.1]⟩).scomp r
      ((hasDerivAt_id r).const_sub T)
    simpa only [one_smul,neg_smul,Function.comp_def] using hd
  have hh := norm_ode_volterra_bound hT (hz.comp hc.continuousOn hm)
    (hdz.neg.comp hc.continuousOn hm) (hb.comp hc.continuousOn hm)
    (fun r hr => hb0 (T-r) (hm hr)) he (fun r hr => by
      simpa only [Function.comp_apply,Pi.neg_apply,norm_neg] using hbound (T-r) (hm hr)) T ⟨hT,le_rfl⟩
  simpa only [Function.comp_apply,sub_self, sub_zero, intervalIntegral.integral_comp_sub_left] using hh

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

lemma characteristic_separation_volterra {E B : Field} {α γ : ℝ → Phase} {T L : ℝ}
    {g : ℝ → ℝ} (hT : 0≤T) (hL : 0≤L)
    (hE : ContDiffOn ℝ 1 E fieldHalfSpace) (hB : ContDiffOn ℝ 1 B fieldHalfSpace)
    (hα : ContinuousOn α (Icc (0:ℝ) T)) (hγ : ContinuousOn γ (Icc (0:ℝ) T))
    (hdα : ∀ r∈Ioo (0:ℝ) T,HasDerivAt α (lorentzField E B (r,α r)) r)
    (hdγ : ∀ r∈Ioo (0:ℝ) T,HasDerivAt γ (lorentzField E B (r,γ r)) r)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖E (r,y)-E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖B (r,y)-B (r,x)‖≤g r*‖y-x‖) :
    ‖α 0-γ 0‖≤‖α T-γ T‖*Real.exp (∫ r in 0..T,1+2*g r+L) := by
  apply backward_norm_ode_volterra_bound hT (hα.sub hγ)
    ((continuousOn_lorentz_along hE hB hα).sub (continuousOn_lorentz_along hE hB hγ))
    ((continuousOn_const.add (continuousOn_const.mul hg)).add continuousOn_const)
    (fun r hr => by change 0≤1+2*g r+L; linarith [hg0 r hr]) (fun r hr => (hdα r hr).sub (hdγ r hr))
  intro r hr
  change ‖lorentzField E B (r,α r)-lorentzField E B (r,γ r)‖≤(1+2*g r+L)*‖α r-γ r‖
  simpa only [mul_zero,add_zero] using lorentzField_difference_bound hL (hg0 r hr)
    (D:=0) le_rfl (hBb r hr) (hEx r hr) (hBx r hr) (by intros; simp) (by intros; simp) (α r) (γ r)

lemma particle_lipschitz_volterra_before {d : Datum} {s : Solution} {T U A L : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hL : 0≤L)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤g r*‖y-x‖)
    (z w : Phase) :
    |s.f (T,z)-s.f (T,w)|≤(A*Real.exp (∫ r in 0..T,1+2*g r+L))*‖z-w‖ := by
  obtain ⟨X,V,hXT,hVT,hX,hV,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 z.1 z.2
  obtain ⟨Y,W,hYT,hWT,hY,hW,_⟩ := exists_characteristic_on_slab hT ⟨hT,le_rfl⟩ hs.2.1 hs.2.2.1 w.1 w.2
  have hXc : ContinuousOn X (Icc 0 T) := fun r hr => (hX r hr).continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := fun r hr => (hV r hr).continuousWithinAt
  have hYc : ContinuousOn Y (Icc 0 T) := fun r hr => (hY r hr).continuousWithinAt
  have hWc : ContinuousOn W (Icc 0 T) := fun r hr => (hW r hr).continuousWithinAt
  have hdX := fun r hr => (hX r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdV := fun r hr => (hV r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdY := fun r hr => (hY r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hdW := fun r hr => (hW r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  have hf := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hXc hVc hdX hdV
  have hf' := transport_on_characteristic_before hs.1 hs.2.2.2.2.2.2.2.1 hT hTU hYc hWc hdY hdW
  rw [hXT,hVT,hs.2.2.2.2.2.2.2.2.1] at hf
  rw [hYT,hWT,hs.2.2.2.2.2.2.2.2.1] at hf'
  have hsep := characteristic_separation_volterra hT hL hs.2.1 hs.2.2.1 (hXc.prodMk hVc) (hYc.prodMk hWc)
    (fun r hr => (hdX r hr).prodMk (hdV r hr)) (fun r hr => (hdY r hr).prodMk (hdW r hr)) hg hg0 hBb hEx hBx
  simp only [hXT,hVT,hYT,hWT,Prod.mk.eta] at hsep
  change |s.f (T,z.1,z.2)-s.f (T,w.1,w.2)|≤_
  rw [hf,hf']
  exact (h₀ (X 0,V 0) (Y 0,W 0)).trans ((mul_le_mul_of_nonneg_left hsep hA).trans_eq (by ring))

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

lemma particle_gradient_volterra_before {d : Datum} {s : Solution} {T U A L : ℝ}
    {g : ℝ → ℝ} (hs : ClassicalBefore d s U) (hT : 0≤T) (hTU : T≤U)
    (hA : 0≤A) (hL : 0≤L)
    (h₀ : ∀ z w,|d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hg : ContinuousOn g (Icc (0:ℝ) T)) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r)
    (hBb : ∀ r∈Icc (0:ℝ) T,∀ x,‖s.B (r,x)‖≤L)
    (hEx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.E (r,y)-s.E (r,x)‖≤g r*‖y-x‖)
    (hBx : ∀ r∈Icc (0:ℝ) T,∀ x y,‖s.B (r,y)-s.B (r,x)‖≤g r*‖y-x‖) :
    ∀ t∈Icc (0:ℝ) T,∀ y v,
      ‖fderiv ℝ (fun z => s.f (t,z,v)) y‖≤A*Real.exp (∫ r in 0..T,1+2*g r+L) := by
  intro t ht y v
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) T := fun r hr => ⟨hr.1,hr.2.trans ht.2⟩
  have hβ : ContinuousOn (fun r => 1+2*g r+L) (Icc (0:ℝ) T) := by fun_prop
  have hI : (∫ r in 0..t,1+2*g r+L)≤∫ r in 0..T,1+2*g r+L := by
    apply intervalIntegral.integral_mono_interval (μ:=volume) le_rfl ht.1 ht.2 _ (hβ.intervalIntegrable_of_Icc hT)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change 0≤1+2*g r+L
    linarith [hg0 r ⟨hr.1.le,hr.2⟩]
  let N := A*Real.exp (∫ r in 0..T,1+2*g r+L)
  have hN : 0≤N := mul_nonneg hA (Real.exp_pos _).le
  have hLip : LipschitzWith ⟨N,hN⟩ (fun z => s.f (t,z,v)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hh := particle_lipschitz_volterra_before hs ht.1 (ht.2.trans hTU) hA hL h₀
      (hg.mono hsub) (fun r hr => hg0 r (hsub hr))
      (fun r hr => hBb r (hsub hr)) (fun r hr => hEx r (hsub hr)) (fun r hr => hBx r (hsub hr)) (a,v) (b,v)
    have hnorm : ‖(a,v)-(b,v)‖=‖a-b‖ := by simp [Prod.norm_def]
    rw [hnorm] at hh
    change ‖s.f (t,a,v)-s.f (t,b,v)‖≤N*‖a-b‖
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hI) hA) (norm_nonneg _))
  exact norm_fderiv_le_of_lipschitz ℝ hLip

universe u

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_FieldGradientNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma curl_norm_le_gradient {F : Vec → Vec} (hF : Differentiable ℝ F) (x : Vec) :
    ‖curl F x‖≤6*‖fderiv ℝ F x‖ := by
  have hb : ∀ i : Fin 3, |curl F x i|≤2*‖fderiv ℝ F x‖ := by
    intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    have hb (j k : Fin 3) : |spatialPartial (fun y => F y k) x j|≤‖fderiv ℝ F x‖ := by
      rw [spatialPartial,coordinate_fderiv_apply hF]
      simpa only [show ‖basis j‖=1 by simp [basis,PiLp.norm_single],mul_one] using
        (norm_coordinate_le _ k).trans ((fderiv ℝ F x).le_opNorm (basis j))
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add (hb _ _) (hb _ _)).trans_eq (by ring))
  exact (norm_le_three_of_coordinate_bound (by positivity) hb).trans_eq (by ring)

lemma full_field_derivative_bound {F : Field} {t : ℝ} {x : Vec}
    (hF : DifferentiableAt ℝ F (t,x)) :
    ‖fderiv ℝ F (t,x)‖≤‖deriv (fun r => F (r,x)) t‖+‖fderiv ℝ (fun y => F (t,y)) x‖ := by
  let L := fderiv ℝ F (t,x)
  have ht := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hx := hF.hasFDerivAt.comp x ((hasFDerivAt_const (c:=t) x).prodMk (hasFDerivAt_id x))
  have hd (v : Vec) : fderiv ℝ (fun y => F (t,y)) x v=L (0,v) := by
    exact congrArg (fun K : Vec →L[ℝ] Vec => K v) hx.fderiv
  have he : deriv (fun r => F (r,x)) t=L (1,0) := ht.deriv
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  have hp : p=p.1 • (1,0)+(0,p.2) := by ext <;> simp
  have hr : L p=p.1 • deriv (fun r => F (r,x)) t+fderiv ℝ (fun y => F (t,y)) x p.2 := by
    rw [he,hd, hp, map_add, map_smul]
    simp
  change ‖L p‖≤_
  rw [hr]
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  have h₁ : ‖p.1‖≤‖p‖ := norm_fst_le p
  have h₂ : ‖p.2‖≤‖p‖ := norm_snd_le p
  have ha := (fderiv ℝ (fun y => F (t,y)) x).le_opNorm p.2
  nlinarith [mul_le_mul_of_nonneg_right h₁ (norm_nonneg (deriv (fun r => F (r,x)) t)),
    mul_le_mul_of_nonneg_left h₂ (norm_nonneg (fderiv ℝ (fun y => F (t,y)) x))]

lemma current_norm_bound_of_momentum {f : Phase → ℝ} {P A : ℝ}
    (hA : 0≤A) (hfA : ∀ y v,|f (y,v)|≤A) (hP : ∀ y v,P<‖v‖ → f (y,v)=0) (x : Vec) :
    ‖current f x‖≤A*(volume (closedBall (0:Vec) P)).toReal := by
  rw [current,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)]
  · exact (norm_setIntegral_le_of_norm_le_const (C:=A) ((isCompact_closedBall (0:Vec) P).measure_lt_top) (by
      intro v _
      rw [norm_smul,Real.norm_eq_abs]
      simpa only [mul_one] using
        mul_le_mul (hfA x v) (norm_velocity_lt_one v).le (norm_nonneg _) hA)).trans_eq (by rfl)
  · intro v hv
    have hh : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    rw [hP x v hh,zero_smul]

lemma maxwell_full_derivative_bound {s : Solution} {U t P A g : ℝ}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (heq : EquationsBefore s U) (ht : 0<t) (htU : t<U)
    (hA : 0≤A) (hfA : ∀ y v,|s.f (t,y,v)|≤A)
    (hP : ∀ y v,P<‖v‖ → s.f (t,y,v)=0)
    (hb : ∀ y,‖fderiv ℝ (fun z => s.E (t,z)) y‖+‖fderiv ℝ (fun z => s.B (t,z)) y‖≤g)
    (x : Vec) :
    ‖fderiv ℝ s.E (t,x)‖≤7*g+A*(volume (closedBall (0:Vec) P)).toReal ∧
    ‖fderiv ℝ s.B (t,x)‖≤7*g+A*(volume (closedBall (0:Vec) P)).toReal := by
  have he := field_differentiableAt_positive hE ht x
  have hm := field_differentiableAt_positive hB ht x
  have hes : Differentiable ℝ (fun y => s.E (t,y)) := fun y =>
    (field_differentiableAt_positive hE ht y).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbs : Differentiable ℝ (fun y => s.B (t,y)) := fun y =>
    (field_differentiableAt_positive hB ht y).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
  have eqE := (heq t ht.le htU).2.1 x
  have eqB := (heq t ht.le htU).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at eqE eqB
  have hcb := curl_norm_le_gradient hbs x
  have hce := curl_norm_le_gradient hes x
  have hj := current_norm_bound_of_momentum (f:=fun z => s.f (t,z)) (P:=P) hA hfA hP x
  have hj0 : 0≤A*(volume (closedBall (0:Vec) P)).toReal := by positivity
  have heb : ‖deriv (fun r => s.E (r,x)) t‖≤6*‖fderiv ℝ (fun z => s.B (t,z)) x‖+A*(volume (closedBall (0:Vec) P)).toReal := by
    have hh : deriv (fun r => s.E (r,x)) t=curl (fun z => s.B (t,z)) x-current (fun z => s.f (t,z)) x := by
      have hh := sub_eq_iff_eq_add.mp eqE
      rw [hh]; abel
    rw [hh]
    exact (norm_sub_le _ _).trans (add_le_add hcb hj)
  have hbb : ‖deriv (fun r => s.B (r,x)) t‖≤6*‖fderiv ℝ (fun z => s.E (t,z)) x‖ := by
    have hh : deriv (fun r => s.B (r,x)) t=-curl (fun z => s.E (t,z)) x := eq_neg_of_add_eq_zero_left eqB
    simpa only [hh,norm_neg] using hce
  have hn := hb x
  constructor
  · have hh := full_field_derivative_bound he
    nlinarith [norm_nonneg (fderiv ℝ (fun z => s.E (t,z)) x),norm_nonneg (fderiv ℝ (fun z => s.B (t,z)) x)]
  · have hh := full_field_derivative_bound hm
    nlinarith [norm_nonneg (fderiv ℝ (fun z => s.E (t,z)) x),norm_nonneg (fderiv ℝ (fun z => s.B (t,z)) x)]

lemma spatial_field_lipschitz_of_gradient {F : Vec → Vec} {L : ℝ}
    (hF : Differentiable ℝ F) (hL : ∀ x,‖fderiv ℝ F x‖≤L) (x y : Vec) :
    ‖F x-F y‖≤L*‖x-y‖ := by
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hF z) (fun z _ => hL z) (mem_univ y) (mem_univ x)

lemma norm_clm_le_nine_components (L : Vec →L[ℝ] Vec) {C : ℝ} (hC : 0≤C)
    (hb : ∀ i j : Fin 3, |L (basis j) i|≤C) : ‖L‖≤9*C := by
  have hb' (j : Fin 3) : ‖L (basis j)‖≤3*C := norm_le_three_of_coordinate_bound hC (fun i => hb i j)
  apply L.opNorm_le_bound (by positivity)
  intro v
  have he : L v=∑ j : Fin 3, v j • L (basis j) := by
    conv_lhs => rw [←sum_basis v]
    simp only [map_sum,map_smul]
  rw [he]
  calc
    _ ≤ ∑ j : Fin 3, ‖v j • L (basis j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖v‖*(3*C) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (norm_coordinate_le v j) (hb' j) (norm_nonneg _) (norm_nonneg v)
    _ = 9*C*‖v‖ := by simp; ring

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma hasDerivAt_vec_component_line {g : Vec → Vec} {x e : Vec} (i : Fin 3)
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun q : ℝ => g (x+q • e) i) ((fderiv ℝ g x e) i) 0 := by
  have hl : HasDerivAt (fun q : ℝ => x+q • e) e 0 := by
    convert ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x using 1 <;> first | rfl | simp
  have hg' : HasFDerivAt g (fderiv ℝ g x) (x+(0:ℝ) • e) := by simpa only [zero_smul,add_zero] using hg.hasFDerivAt
  have hh := hg'.comp_hasDerivAt (0:ℝ) hl
  have hp := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt (0:ℝ) hh
  simpa only [Function.comp_def,PiLp.proj_apply] using hp

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


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

lemma ClassicalBefore.mono {d : Datum} {s : Solution} {T U : ℝ}
    (hs : ClassicalBefore d s U) (hTU : T≤U) : ClassicalBefore d s T := by
  rcases hs with ⟨hf,hE,hB,hn,hEL,hBL,hc,heq,hf₀,hE₀,hB₀⟩
  exact ⟨hf,hE,hB,hn,hEL,hBL,hc,fun t ht h => heq t ht (h.trans_le hTU),hf₀,hE₀,hB₀⟩

lemma log_one_add_mul_exp_le {C A I : ℝ} (hC : 0≤C) (hA : 0≤A) (hI : 0≤I) :
    Real.log (1+C*(A*Real.exp I))≤Real.log (1+C*A)+I := by
  have hCA : 0≤C*A := mul_nonneg hC hA
  have hpos : 0<1+C*A := by linarith
  have he : 1≤Real.exp I := Real.one_le_exp hI
  have hh : 1+C*(A*Real.exp I)≤(1+C*A)*Real.exp I := by nlinarith
  apply (Real.log_le_log (by positivity) hh).trans_eq
  rw [Real.log_mul hpos.ne' (Real.exp_ne_zero _),Real.log_exp]

lemma integral_lorentz_coefficient_bound {g : ℝ → ℝ} {L T : ℝ}
    (hg : Continuous g) (hL : 0≤L) (hT : 0≤T) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r) :
    0≤(∫ r in 0..T,1+2*g r+L) ∧
    (∫ r in 0..T,1+2*g r+L)≤(3+L)*(∫ r in Icc (0:ℝ) T,1+g r) := by
  have hc : Continuous (fun r => 1+2*g r+L) := by fun_prop
  constructor
  · apply intervalIntegral.integral_nonneg hT
    intro r hr
    linarith [hg0 r hr]
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hT,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT (hc.intervalIntegrable 0 T)
      ((continuous_const.mul (continuous_const.add hg)).intervalIntegrable 0 T)
    intro r hr
    change 1+2*g r+L≤(3+L)*(1+g r)
    nlinarith [hg0 r hr,mul_nonneg hL (hg0 r hr)]

lemma classical_magnetic_log_closed_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U t : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y z, ‖s.E (u,y)-s.E (u,z)‖≤g u*‖y-z‖ ∧
        ‖s.B (u,y)-s.B (u,z)‖≤g u*‖y-z‖) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+K*(∫ u in Icc (0:ℝ) U,1+g u) := by
  obtain ⟨B,C,D,K,hB,hC,hD,hK,hv⟩ := Magnetic.classical_magnetic_gradient_volterra_bound hd P A M H e i hA hH
  obtain ⟨A₀,hA₀,hLip⟩ := admissible_particle_lipschitz hd
  refine ⟨B+D*Real.log (1+C*A₀),D*(3+M)+K,?_,by positivity,?_⟩
  · exact add_nonneg hB (mul_nonneg hD (Real.log_nonneg (by nlinarith [mul_nonneg hC hA₀])))
  intro s U t x g hs hm ht htU hUH hg hg0 hfA hP hEB hDF hEx
  have hU : 0≤U := ht.le.trans htU.le
  let N := A₀*Real.exp (∫ r in 0..U,1+2*g r+M)
  have hN : 0≤N := mul_nonneg hA₀ (Real.exp_pos _).le
  have hfN := particle_gradient_volterra_before hs hU le_rfl hA₀ hM hLip hg.continuousOn hg0
    (fun u hu y => (hEB u hu y).2) (fun u hu y z => (hEx u hu z y).1) (fun u hu y z => (hEx u hu z y).2)
  have hh := hv s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  have hi := integral_lorentz_coefficient_bound hg hM hU hg0
  have hlog := log_one_add_mul_exp_le hC hA₀ hi.1
  have hi' : (∫ u in Icc (0:ℝ) t,1+g u)≤∫ u in Icc (0:ℝ) U,1+g u := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le ht.le,←intervalIntegral.integral_of_le hU]
    apply intervalIntegral.integral_mono_interval le_rfl ht.le htU.le _
      ((continuous_const.add hg).intervalIntegrable 0 U)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change 0≤1+g u
    linarith [hg0 u ⟨hu.1.le,hu.2⟩]
  change |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*A₀)+(D*(3+M)+K)*(∫ u in Icc (0:ℝ) U,1+g u)
  dsimp [N] at hh
  nlinarith [mul_le_mul_of_nonneg_left hlog hD,mul_le_mul_of_nonneg_left hi.2 hD,
    mul_le_mul_of_nonneg_left hi' hK]

lemma classical_fields_gradient_current_volterra {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U t : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y z, ‖s.E (u,y)-s.E (u,z)‖≤g u*‖y-z‖ ∧
        ‖s.B (u,y)-s.B (u,z)‖≤g u*‖y-z‖) →
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|+
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨B,K,hB,hK,hE⟩ := classical_electric_log_closed_bound hd P A M H e i hA hM hH
  obtain ⟨D,L,hD,hL,hB'⟩ := classical_magnetic_log_closed_bound hd P A M H e i hA hM hH
  refine ⟨B+D,K+L,add_nonneg hB hD,add_nonneg hK hL,?_⟩
  intro s U t x g hs hm ht htU hUH hg hg0 hfA hP hEB hDF hEx
  have hin : ∀ V∈Ioo t U,
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|+
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤(B+D)+(K+L)*(∫ u in Icc (0:ℝ) V,1+g u) := by
    intro V hV
    have hsub : Icc (0:ℝ) V ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans hV.2.le⟩
    have he := hE s V t x g (hs.mono hV.2.le) hm ht hV.1 (hV.2.le.trans hUH) hg
      (fun u hu => hg0 u (hsub hu)) (fun u hu => hfA u (hsub hu)) (fun u hu => hP u (hsub hu))
      (fun u hu => hEB u (hsub hu)) (fun u hu => hDF u ⟨hu.1,hu.2.trans hV.2.le⟩)
      (fun u hu => hEx u (hsub hu))
    have hb := hB' s V t x g (hs.mono hV.2.le) hm ht hV.1 (hV.2.le.trans hUH) hg
      (fun u hu => hg0 u (hsub hu)) (fun u hu => hfA u (hsub hu)) (fun u hu => hP u (hsub hu))
      (fun u hu => hEB u (hsub hu)) (fun u hu => hDF u ⟨hu.1,hu.2.trans hV.2.le⟩)
      (fun u hu => hEx u (hsub hu))
    linarith
  have hc : ContinuousOn (fun V => (B+D)+(K+L)*(∫ u in Icc (0:ℝ) V,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure hin continuousOn_const
  · rw [_root_.closure_Ioo htU.ne]
    exact hc.mono (fun V hV => ⟨ht.le.trans hV.1,hV.2⟩)
  · simp only [_root_.closure_Ioo htU.ne,mem_Icc,le_refl,htU.le,and_self]

lemma component_le_double_sum {F : Fin 3 → Fin 3 → ℝ} (hF : ∀ i j,0≤F i j) (i j : Fin 3) :
    F i j≤∑ i : Fin 3, ∑ j : Fin 3,F i j := by
  exact (Finset.single_le_sum (fun k _ => hF i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hF k l)) (Finset.mem_univ i))

lemma prefix_spatial_gradient_volterra_oai {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U : ℝ), BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      ∀ g : ℝ → ℝ, Continuous g →
      (∀ u∈Icc (0:ℝ) U, ∀ y,
        ‖fderiv ℝ (fun z => s.E (u,z)) y‖+‖fderiv ℝ (fun z => s.B (u,z)) y‖≤g u) →
      ∀ t∈Icc (0:ℝ) U, ∀ x,
        ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
          B+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  choose B K hB hK hb using fun i j : Fin 3 =>
    classical_fields_gradient_current_volterra hd P A M H (basis j) i hA hM hH
  let D := ∑ i : Fin 3,∑ j : Fin 3,B i j
  let L := ∑ i : Fin 3,∑ j : Fin 3,K i j
  let J := A*(volume (closedBall (0:Vec) P)).toReal
  have hD : 0≤D := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB i j))
  have hL : 0≤L := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK i j))
  have hJ : 0≤J := by dsimp [J]; positivity
  refine ⟨18*D,18*L*(8+J),by positivity,by positivity,?_⟩
  intro s U hs hU hUH hfA hP hEB g hg hgb
  have hg0 : ∀ u∈Icc (0:ℝ) U,0≤g u := fun u hu =>
    (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hgb u hu 0)
  let G : ℝ → ℝ := fun u => 7*g u+J
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hG0 : ∀ u∈Icc (0:ℝ) U,0≤G u := fun u hu => by dsimp [G]; positivity [hg0 u hu]
  have hgG : ∀ u∈Icc (0:ℝ) U,g u≤G u := fun u hu => by dsimp [G]; nlinarith [hg0 u hu]
  have hinterior : ∀ t∈Ioo (0:ℝ) U, ∀ x,
      ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
        18*D+18*L*(8+J)*(∫ u in Icc (0:ℝ) t,1+g u) := by
    intro t ht x
    obtain ⟨τ,htτ,hτU⟩ := exists_between ht.2
    obtain ⟨V,htV,hVτ⟩ := exists_between htτ
    let a := cutoffPrefix τ U s
    have heq (u : ℝ) (hu : u≤τ) := cutoffPrefix_eq hτU hu s
    have ha := hs.classical.cutoff_classical_before (ht.1.le.trans htτ.le) hτU
    have hsub : Icc (0:ℝ) V ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans (hVτ.le.trans hτU.le)⟩
    have hfunE (u : ℝ) (hu : u≤τ) : (fun z => a.E (u,z))=(fun z => s.E (u,z)) := funext (heq u hu).2.1
    have hfunB (u : ℝ) (hu : u≤τ) : (fun z => a.B (u,z))=(fun z => s.B (u,z)) := funext (heq u hu).2.2
    have hab : ∀ u∈Icc (0:ℝ) V,∀ y,
        ‖fderiv ℝ (fun z => a.E (u,z)) y‖+‖fderiv ℝ (fun z => a.B (u,z)) y‖≤g u := by
      intro u hu y
      rw [hfunE u (hu.2.trans hVτ.le),hfunB u (hu.2.trans hVτ.le)]
      exact hgb u (hsub hu) y
    have haA : ∀ u∈Icc (0:ℝ) V,∀ y v,|a.f (u,y,v)|≤A := by
      intro u hu y v
      rw [(heq u (hu.2.trans hVτ.le)).1]
      exact hfA u (hsub hu) y v
    have haP : ∀ u∈Icc (0:ℝ) V,∀ y v,P<‖v‖ → a.f (u,y,v)=0 := by
      intro u hu y v hv
      rw [(heq u (hu.2.trans hVτ.le)).1]
      exact hP u (hsub hu) y v hv
    have haEB : ∀ u∈Icc (0:ℝ) V,∀ y,‖a.E (u,y)‖≤M ∧ ‖a.B (u,y)‖≤M := by
      intro u hu y
      rw [(heq u (hu.2.trans hVτ.le)).2.1,(heq u (hu.2.trans hVτ.le)).2.2]
      exact hEB u (hsub hu) y
    have haDF : ∀ u∈Ioc (0:ℝ) V,∀ y,‖fderiv ℝ a.E (u,y)‖≤G u ∧ ‖fderiv ℝ a.B (u,y)‖≤G u := by
      intro u hu y
      exact maxwell_full_derivative_bound ha.2.1 ha.2.2.1 ha.2.2.2.2.2.2.2.1 hu.1 (hu.2.trans_lt hVτ)
        hA (haA u ⟨hu.1.le,hu.2⟩) (haP u ⟨hu.1.le,hu.2⟩) (hab u ⟨hu.1.le,hu.2⟩) y
    have haLip : ∀ u∈Icc (0:ℝ) V,∀ y z,‖a.E (u,y)-a.E (u,z)‖≤G u*‖y-z‖ ∧
        ‖a.B (u,y)-a.B (u,z)‖≤G u*‖y-z‖ := by
      intro u hu y z
      simp only [a,(heq u (hu.2.trans hVτ.le)).2.1,(heq u (hu.2.trans hVτ.le)).2.2]
      constructor
      · apply spatial_field_lipschitz_of_gradient ((hs.E_jets.1.1 u (hsub hu)).differentiable (by simp))
        intro w
        exact (le_add_of_nonneg_right (norm_nonneg _)).trans ((hgb u (hsub hu) w).trans (hgG u (hsub hu)))
      · apply spatial_field_lipschitz_of_gradient ((hs.B_jets.1.1 u (hsub hu)).differentiable (by simp))
        intro w
        exact (le_add_of_nonneg_left (norm_nonneg _)).trans ((hgb u (hsub hu) w).trans (hgG u (hsub hu)))
    let I := ∫ u in Icc (0:ℝ) t,1+G u
    have hI : 0≤I := by
      apply setIntegral_nonneg measurableSet_Icc
      intro u hu
      linarith [hG0 u ⟨hu.1,hu.2.trans ht.2.le⟩]
    have hcomp (i j : Fin 3) :
        |fderiv ℝ (fun z => s.E (t,z)) x (basis j) i|+
        |fderiv ℝ (fun z => s.B (t,z)) x (basis j) i|≤D+L*I := by
      have hh := hb i j a V t x G (ha.mono hVτ.le) (hs.classical.cutoff_smooth hτU) ht.1 htV
        (hVτ.le.trans (hτU.le.trans hUH)) hG (fun u hu => hG0 u (hsub hu)) haA haP haEB haDF haLip
      simp only [a,(heq t htτ.le).2.1,(heq t htτ.le).2.2] at hh
      rw [(hasDerivAt_vec_component_line i ((hs.E_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)).differentiableAt).deriv,
        (hasDerivAt_vec_component_line i ((hs.B_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)).differentiableAt).deriv] at hh
      exact hh.trans (add_le_add (component_le_double_sum hB i j)
        (mul_le_mul_of_nonneg_right (component_le_double_sum hK i j) hI))
    have hC : 0≤D+L*I := by positivity
    have hEn := norm_clm_le_nine_components (fderiv ℝ (fun z => s.E (t,z)) x) hC
      (fun i j => (le_add_of_nonneg_right (abs_nonneg _)).trans (hcomp i j))
    have hBn := norm_clm_le_nine_components (fderiv ℝ (fun z => s.B (t,z)) x) hC
      (fun i j => (le_add_of_nonneg_left (abs_nonneg _)).trans (hcomp i j))
    have hi : I≤(8+J)*(∫ u in Icc (0:ℝ) t,1+g u) := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc
      · intro u hu
        change 1+(7*g u+J)≤(8+J)*(1+g u)
        nlinarith [hg0 u ⟨hu.1,hu.2.trans ht.2.le⟩,mul_nonneg hJ (hg0 u ⟨hu.1,hu.2.trans ht.2.le⟩)]
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    nlinarith [mul_le_mul_of_nonneg_left hi hL]
  intro t ht x
  have hEc : ContinuousOn (fun r => ‖fderiv ℝ (fun z => s.E (r,z)) x‖) (Icc (0:ℝ) U) := by
    simpa only [Function.comp_def,id_eq,norm_iteratedFDeriv_one] using ((hs.E_jets.1.2 1).comp
      ((continuous_id.prodMk (continuous_const (y:=x))).continuousOn (s:=Icc (0:ℝ) U)) (fun r hr => hr)).norm
  have hBc : ContinuousOn (fun r => ‖fderiv ℝ (fun z => s.B (r,z)) x‖) (Icc (0:ℝ) U) := by
    simpa only [Function.comp_def,id_eq,norm_iteratedFDeriv_one] using ((hs.B_jets.1.2 1).comp
      ((continuous_id.prodMk (continuous_const (y:=x))).continuousOn (s:=Icc (0:ℝ) U)) (fun r hr => hr)).norm
  have hgc : ContinuousOn (fun r => 18*D+18*L*(8+J)*(∫ u in Icc (0:ℝ) r,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure (fun r hr => hinterior r hr x)
  · rw [_root_.closure_Ioo hU.ne]
    intro r hr
    exact (hEc r hr).add (hBc r hr)
  · simpa only [_root_.closure_Ioo hU.ne] using hgc
  · simpa only [_root_.closure_Ioo hU.ne] using ht

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.prefix_spatial_gradient_volterra_oai := @OAI.RVM.prefix_spatial_gradient_volterra_oai
