-- Prove2me | solution 1 for OAI.ScalarConductivity.fourierMatchingFamily_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:12.756137+00:00
-- url     : https://prove2.me/submissions/65df253a-6206-4918-9ada-6316dd5951c5

import Mathlib
import Definitions.Def_OAIQ059C008

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_HadamardWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallQuotient_zero {f : E × ℝ → ℝ} (x : E) :
    wallQuotient f (x,0)=wallDerivative f (x,0) := by
  simp [wallQuotient]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_QuantitativeLocalTwoFieldSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma contDiffAt_matrix_det {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) : ContDiffAt ℝ k (fun y => (A y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun σ _ => contDiffAt_const.mul
    (contDiffAt_prod (fun i _ => contDiffAt_pi.mp (contDiffAt_pi.mp hA (σ i)) i)))

lemma contDiffAt_matrix_inv {X n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype n] [DecidableEq n] {k : WithTop ℕ∞} {A : X → Matrix n n ℝ} {x : X}
    (hA : ContDiffAt ℝ k A x) (hd : (A x).det ≠ 0) :
    ContDiffAt ℝ k (fun y => (A y)⁻¹) x := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  apply ((contDiffAt_matrix_det hA).inv hd).smul
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  simp_rw [Matrix.adjugate_apply]
  apply contDiffAt_matrix_det
  apply contDiffAt_pi.mpr; intro l
  apply contDiffAt_pi.mpr; intro r
  by_cases hl : l = j
  · subst l; simpa only [Matrix.updateRow_self] using
      (contDiffAt_const : ContDiffAt ℝ k (fun _ : X => (Pi.single i (1:ℝ) : n → ℝ) r) x)
  · simpa only [Matrix.updateRow_ne hl] using
      (contDiffAt_pi.mp (contDiffAt_pi.mp hA l) r)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothPhysicalMomentFamily
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma compact_supported_integral_smooth {f : P×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ q,tsupport (fun x => f (q,x))⊆K) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∫ x,f (q,x)) := by
  have he (q : P) : (∫ x in K,f (q,x))=∫ x,f (q,x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun h => hx (hs q h)))
  simpa only [he] using contDiff_compact_integral (μ:=volume) hf hK

lemma physicalSourceMoment_family_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ q,PairSupported (fun j x => r j (q,x)) K) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact compact_supported_integral_smooth (hr 0) hK (fun q => hs q 0)
  · exact compact_supported_integral_smooth (hr 1) hK (fun q => hs q 1)
  · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∫ x,u (q,x) 1*r 0 (q,x)-u (q,x) 0*r 1 (q,x))
    apply compact_supported_integral_smooth
      (((contDiff_apply ℝ ℝ 1).comp hu).mul (hr 0) |>.sub (((contDiff_apply ℝ ℝ 0).comp hu).mul (hr 1))) hK
    intro q
    exact (tsupport_sub _ _).trans (union_subset
      (tsupport_mul_subset_right.trans (hs q 0)) (tsupport_mul_subset_right.trans (hs q 1)))

lemma exists_physical_moments_at_regular
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {O : Set Coord3} (hO : IsOpen O) {x : Coord3} (hx : x∈O)
    (hD : Function.Surjective (fderiv ℝ u x)) (m : Coord3) :
    ∃ r : PhysicalSourcePair,CompactSmoothPair r ∧ PairSupported r O ∧
      physicalSourceMoment u r=m := by
  obtain ⟨B,_⟩ := exists_regular_correction_box hu hO hx hD
  obtain ⟨r₀,r₁,hr₀,hr₁,hc₀,hc₁,hs₀,hs₁,hm₀,hm₁,hmt⟩ :=
    physical_overlap_moment_inverse B.chart B.smooth B.inverse_smooth B.widths B.subset_source m
  let r : PhysicalSourcePair := ![r₀,r₁]
  have hr : CompactSmoothPair r := by
    intro j; fin_cases j
    · exact ⟨hr₀,hc₀⟩
    · exact ⟨hr₁,hc₁⟩
  have hs : PairSupported r B.chart.target := by
    intro j; fin_cases j
    · exact hs₀
    · exact hs₁
  refine ⟨r,hr,hs.mono B.target_subset,?_⟩
  ext i
  fin_cases i
  · exact hm₀
  · exact hm₁
  · change (∫ x,u x 1*r₀ x-u x 0*r₁ x)=m 2
    rw [←hmt]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈B.chart.target
    · rw [B.potentials hy]; rfl
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs₀ h)),
        image_eq_zero_of_notMem_tsupport (fun h => hy (hs₁ h))]
      simp

lemma exists_smooth_matrix_inverse_extension {A : P → Mat3}
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) A) (p : P) (hp : (A p).det≠0) :
    ∃ B : P→Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) B ∧ ∀ᶠ q in 𝓝 p,B q=(A q)⁻¹ := by
  let O := {q : P | (A q).det≠0}
  have hO : IsOpen O := isOpen_ne.preimage (hA.continuous.matrix_det)
  have hI : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => (A q)⁻¹) O :=
    fun q hq => (contDiffAt_matrix_inv hA.contDiffAt hq).contDiffWithinAt
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton
    (hO.inter Metric.isOpen_ball) (Metric.isBounded_ball.subset inter_subset_right)
    (show ({p}:Set P)⊆O∩Metric.ball p 1 from singleton_subset_iff.mpr ⟨hp,Metric.mem_ball_self zero_lt_one⟩)
  refine ⟨fun q => χ q • (A q)⁻¹,?_,?_⟩
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact smooth_mul_of_support_in_open hO
      (by
        intro q hq
        exact ((contDiff_apply ℝ ℝ j).contDiffAt.comp_contDiffWithinAt q
          ((contDiff_apply ℝ (Fin 3 → ℝ) i).contDiffAt.comp_contDiffWithinAt q (hI q hq))))
      hχ (hχs.trans inter_subset_left)
  · filter_upwards [hχone p (mem_singleton p)] with q hq
    rw [hq,one_smul]

theorem smooth_physical_moment_family
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {O : Set Coord3} (hO : IsOpen O) {x : Coord3} (hx : x∈O)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {m : P → Coord3} (hm : ContDiff ℝ (↑(⊤:ℕ∞)) m) (hmz : m p=0) :
    ∃ K : Set Coord3,IsCompact K ∧ K⊆O ∧
      ∃ r : Fin 2 → P×Coord3 → ℝ,(∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) ∧
        (∀ q,PairSupported (fun j y => r j (q,y)) K) ∧ (∀ j y,r j (p,y)=0) ∧
        ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))=m q := by
  classical
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (p,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  choose g hg hs hgm using fun i : Fin 3 =>
    exists_physical_moments_at_regular hup hO hx hD (Pi.single i 1)
  let K := ⋃ i : Fin 3,⋃ j : Fin 2,tsupport (g i j)
  have hK : IsCompact K := isCompact_iUnion (fun i => isCompact_iUnion (fun j => (hg i j).2))
  have hKO : K⊆O := iUnion_subset (fun i => iUnion_subset (hs i))
  have hgK (i) : PairSupported (g i) K := fun j => subset_iUnion_of_subset i (subset_iUnion (fun j => tsupport (g i j)) j)
  let A : P→Mat3 := fun q i j => physicalSourceMoment (fun y => u (q,y)) (g j) i
  have hA : ContDiff ℝ (↑(⊤:ℕ∞)) A := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact (contDiff_apply ℝ ℝ i).comp (physicalSourceMoment_family_smooth hu
      (fun k => (hg j k).1.comp contDiff_snd) hK (fun _ => hgK j))
  have hAp : A p=1 := by
    ext i j
    simp [A,hgm,Pi.single_apply,Matrix.one_apply]
  obtain ⟨B,hB,hBi⟩ := exists_smooth_matrix_inverse_extension hA p (by rw [hAp]; simp)
  let c : P → Coord3 := fun q => B q*ᵥm q
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) c := by
    apply contDiff_pi.mpr; intro i
    change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∑ j : Fin 3,B q i j*m q j)
    exact ContDiff.sum (fun j _ => ((contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 3 → ℝ) i).comp hB)).mul ((contDiff_apply ℝ ℝ j).comp hm))
  let r : Fin 2 → P×Coord3 → ℝ := fun j z => ∑ i,c z.1 i*g i j z.2
  have hr (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (r j) :=
    ContDiff.sum (fun i _ => (((contDiff_apply ℝ ℝ i).comp hc).comp contDiff_fst).mul ((hg i j).1.comp contDiff_snd))
  have hre (q) : (fun j y => r j (q,y))=∑ i,c q i • g i := by
    funext j y; simp [r,Finset.sum_apply]
  have hrs (q) : PairSupported (fun j y => r j (q,y)) K := by
    rw [hre]
    exact PairSupported.sum _ _ (fun i _ => (hgK i).smul _)
  have hrz (j) (y) : r j (p,y)=0 := by simp [r,c,hmz]
  refine ⟨K,hK,hKO,r,hr,hrs,hrz,?_⟩
  have hnear : ∀ᶠ q in 𝓝 p,(A q).det≠0 :=
    hA.continuous.matrix_det.continuousAt.eventually (isOpen_ne.mem_nhds (by change (A p).det≠0; rw [hAp]; simp))
  filter_upwards [hBi,hnear] with q hq hdet
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  rw [hre,physicalSourceMoment_sum _ _ huq.continuous
    (fun i _ => (hg i).smul _)]
  simp_rw [physicalSourceMoment_smul]
  have hi : A q*ᵥc q=m q := by
    dsimp [c]
    rw [hq,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  ext i
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,Matrix.mulVec,dotProduct,A] using congrFun hi i

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_SmoothFamilyCorrectionTransport
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SmoothVanishingPairFamily
omit [FiniteDimensional ℝ P]
variable {p : P} {W V : Set Coord3} {r s : Fin 2 → P×Coord3 → ℝ}
lemma mono (hr : SmoothVanishingPairFamily p W r) (hWV : W⊆V) :
    SmoothVanishingPairFamily p V r := by
  obtain ⟨hsm,hz,K,hK,hKW,hs⟩ := hr
  exact ⟨hsm,hz,K,hK,hKW.trans hWV,hs⟩
lemma sub (hr : SmoothVanishingPairFamily p W r) (hs : SmoothVanishingPairFamily p W s) :
    SmoothVanishingPairFamily p W (r-s) := by
  obtain ⟨hr,hrz,K,hK,hKW,hKr⟩ := hr
  obtain ⟨hs,hsz,L,hL,hLW,hLs⟩ := hs
  exact ⟨fun j => (hr j).sub (hs j),fun j x => by simp [hrz,hsz],
    K∪L,hK.union hL,union_subset hKW hLW,fun q =>
      ((hKr q).mono subset_union_left).sub ((hLs q).mono subset_union_right)⟩
end SmoothVanishingPairFamily

theorem VanishingCorrectionRegion.smooth_transfer
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (B C : VanishingCorrectionRegion u p U) {x : Coord3}
    (hx : x∈B.region∩C.region)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p B.region r) :
    ∃ s : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p C.region s ∧
      (∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => s j (q,y))=
        physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U
          ((fun j y => r j (q,y))-(fun j y => s j (q,y))) ε := by
  obtain ⟨K,hK,hKW,hs⟩ := hr.2.2
  let m : P → Coord3 := fun q => physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) m := physicalSourceMoment_family_smooth hu hr.1 hK hs
  have hmz : m p=0 := by
    change physicalSourceMoment (fun y => u (p,y)) (fun j y => r j (p,y))=0
    rw [show (fun j y => r j (p,y))=0 by funext j y; exact hr.2.1 j y,physicalSourceMoment_zero]
  obtain ⟨L,hL,hLO,s,hsm,hss,hsz,hsmom⟩ := smooth_physical_moment_family hu p
    (B.region_open.inter C.region_open) hx hD hm hmz
  have hsf : SmoothVanishingPairFamily p (B.region∩C.region) s := ⟨hsm,hsz,L,hL,hLO,hss⟩
  refine ⟨s,hsf.mono inter_subset_right,hsmom,?_⟩
  intro ε hε
  have hsolve := B.solve (r-s) (hr.sub (hsf.mono inter_subset_left)) ε hε
  filter_upwards [hsolve,hsmom] with q solve mom
  apply solve
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  change physicalSourceMoment (fun y => u (q,y))
    ((fun j y => r j (q,y))-(fun j y => s j (q,y)))=0
  rw [physicalSourceMoment_sub huq.continuous (hr.compact q) (hsf.compact q),mom,sub_self]

theorem smooth_chain_source_transport
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    {B C : VanishingCorrectionRegion u p U}
    (hpath : Relation.TransGen (fun B C : VanishingCorrectionRegion u p U =>
      ∃ x∈B.region∩C.region,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) B C) :
    ∀ {r : Fin 2 → P×Coord3 → ℝ},SmoothVanishingPairFamily p B.region r →
    ∃ s : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p C.region s ∧
      (∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => s j (q,y))=
        physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U
          ((fun j y => r j (q,y))-(fun j y => s j (q,y))) ε := by
  induction hpath with
  | @single C h =>
    obtain ⟨x,hx,hD⟩ := h
    exact fun hr => B.smooth_transfer hu p C hx hD hr
  | @tail C D hpath hCD ih =>
    intro r hr
    obtain ⟨s,hs,hsm,hsc⟩ := ih hr
    obtain ⟨x,hx,hD⟩ := hCD
    obtain ⟨t,ht,htm,htc⟩ := C.smooth_transfer hu p D hx hD hs
    refine ⟨t,ht,?_,?_⟩
    · filter_upwards [hsm,htm] with q hq htq
      exact htq.trans hq
    · intro ε hε
      filter_upwards [hsc (ε/2) (by linarith),htc (ε/2) (by linarith)] with q hq htq
      have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) :=
        hu.comp (contDiff_const.prodMk contDiff_id)
      have h := hq.add huq htq
      rw [sub_add_sub_cancel] at h
      simpa only [add_halves] using h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma angularShift_add (T : ℝ) (n m : Fin 2 → ℤ) :
    angularShift T (n+m)=angularShift T n+angularShift T m := by
  ext i
  fin_cases i <;> simp [angularShift,mul_add]
lemma angularShift_succ (T : ℝ) (n : Fin 2 → ℤ) (i : Fin 2) :
    angularShift T n i.succ=T*(n i:ℝ) := by fin_cases i <;> rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma angularPeriodize_periodic (T : ℝ) (f : Coord3 → E) :
    AngularPeriodic T (angularPeriodize T f) := by
  intro n x
  unfold angularPeriodize
  calc
    _ = ∑ᶠ m : Fin 2 → ℤ,f (x+angularShift T (m+n)) := by
      congr 1
      funext m
      rw [angularShift_add]
      congr 1
      abel
    _ = _ := finsum_comp_equiv (Equiv.addRight n) (f := fun m => f (x+angularShift T m))

omit [NormedSpace ℝ E] in
lemma angular_translates_locallyFinite {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hc : HasCompactSupport f) :
    LocallyFinite (fun n : Fin 2 → ℤ => Function.support (fun x => f (x+angularShift T n))) := by
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  intro x
  obtain ⟨N,hN⟩ := exists_nat_gt ((R+‖x‖+1)/T)
  refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,?_⟩
  apply (Set.finite_Icc (fun _ : Fin 2 => -(N:ℤ)) (fun _ => (N:ℤ))).subset
  rintro n ⟨z,hz,hzx⟩
  have hzs : z+angularShift T n∈tsupport f := subset_tsupport f hz
  have hzn : ‖z‖<‖x‖+1 := by
    have hh : ‖z‖ ≤ ‖x‖+dist z x := by
      simpa only [dist_eq_norm,add_comm,norm_sub_rev] using norm_le_norm_add_norm_sub x z
    linarith [Metric.mem_ball.mp hzx]
  have hsn : ‖angularShift T n‖<R+‖x‖+1 := by
    have he : angularShift T n=(z+angularShift T n)-z := by abel
    rw [he]
    exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith [hR _ hzs])
  have hi (i : Fin 2) : |(n i:ℝ)|<(N:ℝ) := by
    have hh := (norm_le_pi_norm (angularShift T n) i.succ).trans_lt hsn
    rw [angularShift_succ,Real.norm_eq_abs,abs_mul,abs_of_pos hT] at hh
    exact (lt_div_iff₀ hT).mpr (by simpa only [mul_comm] using hh) |>.trans hN
  constructor
  · intro i
    have hh := (abs_lt.mp (hi i)).1.le
    exact_mod_cast hh
  · intro i
    have hh := (abs_lt.mp (hi i)).2.le
    exact_mod_cast hh

lemma angularPeriodize_smooth {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hc : HasCompactSupport f) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (angularPeriodize T f) := by
  rw [←contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun n => (contMDiff_iff_contDiff).mpr
    (hf.comp (contDiff_id.add contDiff_const))) (angular_translates_locallyFinite hT hc)

omit [NormedSpace ℝ E] in
lemma angularPeriodize_local_sum {T : ℝ} (hT : 0<T)
    {f : Coord3 → E} (hc : HasCompactSupport f) (x : Coord3) :
    ∃ s : Finset (Fin 2 → ℤ),∀ᶠ y in 𝓝 x,
      angularPeriodize T f y=∑ n∈s,f (y+angularShift T n) ∧
      ∀ n,n∉s → f (y+angularShift T n)=0 := by
  classical
  obtain ⟨N,hN,hfin⟩ := angular_translates_locallyFinite hT hc x
  refine ⟨hfin.toFinset,?_⟩
  filter_upwards [hN] with y hy
  have hz (n) (hn : n∉hfin.toFinset) : f (y+angularShift T n)=0 := by
    by_contra h
    exact hn (hfin.mem_toFinset.mpr ⟨y,h,hy⟩)
  exact ⟨finsum_eq_sum_of_support_subset _ (by
    intro n hn
    by_contra h
    exact hn (hz n h)),hz⟩

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma AngularPeriodic.fderiv {T : ℝ} {f : Coord3 → E} (hf : AngularPeriodic T f) :
    AngularPeriodic T (fderiv ℝ f) := by
  intro n x
  have he : (fun y => f (y+angularShift T n))=f := funext (hf n)
  rw [←fderiv_comp_add_right,he]

lemma coordinateDivergence_comp_add (F : Coord3 → Coord3) (a x : Coord3) :
    coordinateDivergence (fun y => F (y+a)) x=coordinateDivergence F (x+a) := by
  unfold coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_comp_add_right (f:=fun y => F y i)]

lemma symmetricSource_congr_nhds {H K : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    {x : Coord3} (h : H=ᶠ[𝓝 x] K) (j : Fin 2) :
    symmetricSource H u j x=symmetricSource K u j x := by
  unfold symmetricSource coordinateDivergence
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => (H y*gradientColumns (fderiv ℝ u y)).col j i)=ᶠ[𝓝 x]
      (fun y => (K y*gradientColumns (fderiv ℝ u y)).col j i) := by
    filter_upwards [h] with y hy
    rw [hy]
  rw [he.fderiv_eq]

lemma symmetricSource_finset_sum {ι : Type*} (s : Finset ι) (H : ι → Coord3 → Mat3)
    (hH : ∀ i∈s,ContDiff ℝ (↑(⊤:ℕ∞)) (H i))
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) :
    symmetricSource (∑ i∈s,H i) u j=∑ i∈s,symmetricSource (H i) u j := by
  classical
  induction s using Finset.induction with
  | empty => simp [symmetricSource_zero]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hsum : ContDiff ℝ (↑(⊤:ℕ∞)) (∑ i∈s,H i) := by
      convert (ContDiff.sum (fun i hi => hH i (Finset.mem_insert_of_mem hi))) using 1
      all_goals try with_reducible_and_instances rfl
      funext y; simp only [Finset.sum_apply]
    rw [symmetricSource_add (hH a (Finset.mem_insert_self _ _)) hsum hu j,
      ih (fun i hi => hH i (Finset.mem_insert_of_mem hi))]

lemma symmetricSource_angular_translate {T : ℝ} {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic T u) (H : Coord3 → Mat3) (j : Fin 2) (n : Fin 2 → ℤ) (x : Coord3) :
    symmetricSource (fun y => H (y+angularShift T n)) u j x=
      symmetricSource H u j (x+angularShift T n) := by
  have he : (fun y => (H (y+angularShift T n)*gradientColumns (fderiv ℝ u y)).col j)=
      (fun y => (H (y+angularShift T n)*gradientColumns (fderiv ℝ u (y+angularShift T n))).col j) := by
    funext y
    rw [hu.fderiv n y]
  unfold symmetricSource
  rw [he]
  exact coordinateDivergence_comp_add (fun y => (H y*gradientColumns (fderiv ℝ u y)).col j) _ _

theorem symmetricSource_angularPeriodize {T : ℝ} (hT : 0<T)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hp : AngularPeriodic T u)
    (j : Fin 2) (x : Coord3) :
    symmetricSource (angularPeriodize T H) u j x=angularPeriodize T (symmetricSource H u j) x := by
  classical
  obtain ⟨s,hs⟩ := angularPeriodize_local_sum hT hc x
  have he : angularPeriodize T H=ᶠ[𝓝 x] ∑ n∈s,(fun y => H (y+angularShift T n)) := by
    filter_upwards [hs] with y hy
    simpa only [Finset.sum_apply] using hy.1
  rw [symmetricSource_congr_nhds he j,
    symmetricSource_finset_sum s (fun n y => H (y+angularShift T n))
      (fun n _ => hH.comp (contDiff_id.add (contDiff_const (c:=angularShift T n)))) hu j]
  simp only [Finset.sum_apply,symmetricSource_angular_translate hp]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hns
  have hz : (fun y => H (y+angularShift T n))=ᶠ[𝓝 x] (0 : Coord3 → Mat3) :=
    hs.mono (fun _ h => h.2 n hns)
  have hh := symmetricSource_congr_nhds (u:=u) hz j
  rw [symmetricSource_angular_translate hp,symmetricSource_zero] at hh
  exact hn hh

lemma angularPeriodize_symmetric {T : ℝ} (hT : 0<T) {H : Coord3 → Mat3}
    (hc : HasCompactSupport H) (hs : ∀ x,(H x).IsSymm) (x : Coord3) :
    (angularPeriodize T H x).IsSymm := by
  obtain ⟨s,h⟩ := angularPeriodize_local_sum hT hc x
  rw [(h.self_of_nhds).1]
  classical
  change (∑ n∈s,H (x+angularShift T n))ᵀ=∑ n∈s,H (x+angularShift T n)
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl (fun n _ => hs _)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_FlatTorusPDE
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma expCosLinear_deriv (L K : E →L[ℝ] ℝ) (p : ℝ) (x : E) :
    HasFDerivAt (expCosLinear L K p)
      (expCosLinear L K p x • L + expCosLinear L K (p+Real.pi/2) x • K) x := by
  have hh := (L.hasFDerivAt (x := x)).exp.mul ((K.hasFDerivAt.add_const p).cos)
  convert hh using 1 <;> ext v <;>
    simp [smul_eq_mul,expCosLinear,Pi.mul_apply,←add_assoc,cos_add_pi_div_two]
  ring

lemma expCosLinear_fderiv (L K : E →L[ℝ] ℝ) (p : ℝ) (x v : E) :
    fderiv ℝ (expCosLinear L K p) x v =
      expCosLinear L K p x*L v+expCosLinear L K (p+Real.pi/2) x*K v := by
  rw [(expCosLinear_deriv L K p x).fderiv]
  rfl

lemma expCosLinear_hessian (L K : E →L[ℝ] ℝ) (p : ℝ) (x v w : E) :
    (iteratedFDeriv ℝ 2 (expCosLinear L K p) x) ![v,w] =
      (L v*L w-K v*K w)*expCosLinear L K p x+
      (L v*K w+K v*L w)*expCosLinear L K (p+Real.pi/2) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (expCosLinear L K p)) x := by
    have hc : ContDiff ℝ 2 (expCosLinear L K p) := by unfold expCosLinear; fun_prop
    exact (hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have he := fderiv_clm_apply (c := fderiv ℝ (expCosLinear L K p)) hd
    (differentiableAt_const (c := w))
  have hfun : (fun y => fderiv ℝ (expCosLinear L K p) y w)=
      fun y => expCosLinear L K p y*L w+expCosLinear L K (p+Real.pi/2) y*K w := by
    funext y
    exact expCosLinear_fderiv L K p y w
  rw [hfun] at he
  have hh := ((expCosLinear_deriv L K p x).mul_const (L w)).add
    ((expCosLinear_deriv L K (p+Real.pi/2) x).mul_const (K w))
  have hhe := hh.fderiv
  change fderiv ℝ (fun y => expCosLinear L K p y*L w+
    expCosLinear L K (p+Real.pi/2) y*K w) x=_ at hhe
  rw [hhe] at he
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A v) he
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
    ContinuousLinearMap.flip_apply,add_apply,smul_apply,
    smul_eq_mul] at hv
  rw [←hv]
  have hp : p+Real.pi/2+Real.pi/2=p+Real.pi := by ring
  simp only [expCosLinear,hp,←add_assoc,cos_add_pi]
  ring

lemma flatPhaseMode_harmonic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) (p : ℝ) (x : Fin 3 → ℝ) :
    flatTensorLaplacian s (flatPhaseMode s h p) x=0 := by
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ := -torusRate s h • ContinuousLinearMap.proj 0
  have hf : flatPhaseMode s h p=expCosLinear L (torusAngular h) p := rfl
  have hsq : torusRate s h^2=torusQuadratic s h := by
    apply sq_sqrt
    exact (by positivity : 0≤(1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2)).trans (hs _ _)
  rw [flatTensorLaplacian,hf]
  simp only [flatTensorLaplacianCLM,add_apply,
    smul_apply,ContinuousMultilinearMap.apply_apply,smul_eq_mul,
    expCosLinear_hessian]
  simp only [L,torusAngular,add_apply,smul_apply,
    ContinuousLinearMap.proj_apply,flatAxis,Pi.single_apply,smul_eq_mul]
  simp only [show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide,
    show (2:Fin 3)≠1 by decide,show (2:Fin 3)≠0 by decide,
    show (0:Fin 3)≠1 by decide,show (1:Fin 3)≠0 by decide,
    ite_true,ite_false,mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero,
    zero_sub,neg_mul,neg_neg,mul_neg]
  dsimp [torusQuadratic] at hsq
  have hm := congrArg (fun r => r*expCosLinear L (torusAngular h) p x) hsq
  dsimp [L,torusAngular] at hm
  linear_combination hm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FlatFourierFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatModeFlux_divergence {s : Fin 3 → ℝ} {f : Coord3 → ℝ} {x : Coord3}
    (hf : ContDiffAt ℝ (↑(⊤:ℕ∞)) f x) :
    coordinateDivergence (flatModeFlux s f) x=flatTensorLaplacian s f x := by
  have hd := (hf.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞)≤⊤))).differentiableAt (by simp)
  have he (i : Fin 3) :
      fderiv ℝ (fun y => fderiv ℝ f y (flatAxis i)) x=(fderiv ℝ (fderiv ℝ f) x).flip (flatAxis i) := by
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have he' (i : Fin 3) : DifferentiableAt ℝ (fun y => fderiv ℝ f y (flatAxis i)) x :=
    hd.clm_apply (differentiableAt_const _)
  have hsum := hf.isSymmSndFDerivAt (by simp)
  unfold coordinateDivergence
  rw [Fin.sum_univ_three]
  change fderiv ℝ (fun y => fderiv ℝ f y (flatAxis 0)) x (flatAxis 0)+
    fderiv ℝ (fun y => s 0*fderiv ℝ f y (flatAxis 1)+s 1*fderiv ℝ f y (flatAxis 2)) x (flatAxis 1)+
    fderiv ℝ (fun y => s 1*fderiv ℝ f y (flatAxis 1)+s 2*fderiv ℝ f y (flatAxis 2)) x (flatAxis 2)=_
  rw [fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _),
    fderiv_fun_add ((he' 1).const_mul _) ((he' 2).const_mul _)]
  simp only [fderiv_const_mul (he' _),he,_root_.add_apply,
    _root_.smul_apply,ContinuousLinearMap.flip_apply,smul_eq_mul]
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [hsum.eq (flatAxis 2) (flatAxis 1)]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothAngularCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma periodCutoff_smooth (T : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (periodCutoff T) :=
  (smoothTransition.contDiff.comp ((contDiff_id.div_const T).add contDiff_const)).sub
    (smoothTransition.contDiff.comp (contDiff_id.div_const T))

lemma periodCutoff_zero_left {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x≤-T) :
    periodCutoff T x=0 := by
  have hh : x/T≤-1 := (div_le_iff₀ hT).mpr (by linarith)
  rw [periodCutoff,smoothTransition.zero_of_nonpos (by linarith),
    smoothTransition.zero_of_nonpos (by linarith),sub_self]

lemma periodCutoff_zero_right {T : ℝ} (hT : 0<T) {x : ℝ} (hx : T≤x) :
    periodCutoff T x=0 := by
  have hh : 1≤x/T := (le_div_iff₀ hT).mpr (by linarith)
  rw [periodCutoff,smoothTransition.one_of_one_le (by linarith),
    smoothTransition.one_of_one_le hh,sub_self]

lemma periodCutoff_support {T : ℝ} (hT : 0<T) : tsupport (periodCutoff T)⊆Icc (-T) T := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra h
    exact hx (periodCutoff_zero_left hT (le_of_not_ge h))
  · by_contra h
    exact hx (periodCutoff_zero_right hT (le_of_not_ge h))

lemma periodCutoff_partition {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T) :
    periodCutoff T x+periodCutoff T (x-T)=1 := by
  have hz : 0≤x/T := div_nonneg hx.1 hT.le
  have h1 : x/T≤1 := (div_le_one hT).mpr hx.2
  have he : (x-T)/T+1=x/T := by field_simp; ring
  rw [periodCutoff,periodCutoff,he,
    smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) hT.le)]
  ring

lemma periodCutoff_support_translate {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T)
    {n : ℤ} (hn : periodCutoff T (x+T*n)≠0) : n=-1 ∨ n=0 := by
  by_contra h
  have hh : n≤-2 ∨ 1≤n := by omega
  rcases hh with hh | hh
  · have hc : (n:ℝ)≤-2 := by exact_mod_cast hh
    exact hn (periodCutoff_zero_left hT (by nlinarith [hx.1,hx.2,mul_le_mul_of_nonneg_left hc hT.le]))
  · have hc : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hh
    exact hn (periodCutoff_zero_right hT (by nlinarith [hx.1,hx.2,mul_le_mul_of_nonneg_left hc hT.le]))

lemma periodCutoff_finsum_core {T : ℝ} (hT : 0<T) {x : ℝ} (hx : x∈Icc 0 T) :
    (∑ᶠ n : ℤ,periodCutoff T (x+T*n))=1 := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s:={-1,0}) (by
    intro n hn
    simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using
      periodCutoff_support_translate hT hx hn)]
  simp only [Finset.sum_insert (by norm_num : (-1:ℤ)∉({0}:Finset ℤ)),Finset.sum_singleton,
    Int.cast_neg,Int.cast_one,Int.cast_zero,mul_neg_one,mul_zero,add_zero]
  simpa only [sub_eq_add_neg,add_comm] using periodCutoff_partition hT hx

lemma periodCutoff_finsum {T : ℝ} (hT : 0<T) (x : ℝ) :
    (∑ᶠ n : ℤ,periodCutoff T (x+T*n))=1 := by
  let m : ℤ := ⌊x/T⌋
  let y := x-T*m
  have hy : y∈Icc 0 T := by
    have ha := Int.floor_le (x/T)
    have hb := Int.lt_floor_add_one (x/T)
    constructor
    · dsimp [y,m]
      have hh := (le_div_iff₀ hT).mp ha
      nlinarith
    · dsimp [y,m]
      have hh := (div_lt_iff₀ hT).mp hb
      nlinarith
  have he := finsum_comp_equiv (Equiv.addRight m)
    (f:=fun n : ℤ => periodCutoff T (y+T*n))
  have hf : (fun n : ℤ => periodCutoff T (y+T*((n+m:ℤ):ℝ)))=
      (fun n : ℤ => periodCutoff T (x+T*n)) := by
    funext n
    congr 1
    simp only [y,Int.cast_add]
    ring
  change (∑ᶠ n : ℤ,periodCutoff T (y+T*((n+m:ℤ):ℝ)))=_ at he
  rw [hf,periodCutoff_finsum_core hT hy] at he
  exact he

theorem periodCutoff_integral {T : ℝ} (hT : 0<T) {g : ℝ → ℝ}
    (hg : Continuous g) (hp : Function.Periodic g T) :
    (∫ x,periodCutoff T x*g x)=∫ x in (0:ℝ)..T,g x := by
  let f := fun x => periodCutoff T x*g x
  have hf : Continuous f := (periodCutoff_smooth T).continuous.mul hg
  have hs : Function.support f⊆Ioc (-T) T := by
    intro x hx
    constructor
    · by_contra h
      exact hx (by simp [f,periodCutoff_zero_left hT (le_of_not_gt h)])
    · by_contra h
      exact hx (by simp [f,periodCutoff_zero_right hT (le_of_not_ge h)])
  rw [←intervalIntegral.integral_eq_integral_of_support_subset hs,
    ←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-T) 0) (hf.intervalIntegrable 0 T)]
  have he : (∫ x in -T..(0:ℝ),f x)=∫ x in (0:ℝ)..T,f (x-T) := by
    rw [intervalIntegral.integral_comp_sub_right]
    simp
  rw [he]
  have hi : IntervalIntegrable (fun x => f (x-T)) volume 0 T :=
    (hf.comp (continuous_id.sub continuous_const)).intervalIntegrable 0 T
  rw [←intervalIntegral.integral_add hi (hf.intervalIntegrable 0 T)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc 0 T := by simpa only [uIcc_of_le hT.le] using hx
  have hgp : g (x-T)=g x := by simpa using hp.sub_eq x
  dsimp [f]
  rw [hgp,←add_mul]
  rw [add_comm (periodCutoff T (x-T)),periodCutoff_partition hT hx',one_mul]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularLocalizedSources
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma angularCutoff_smooth (T : ℝ) : ContDiff ℝ (↑(⊤:ℕ∞)) (angularCutoff T) :=
  ((periodCutoff_smooth T).comp (by fun_prop)).mul
    ((periodCutoff_smooth T).comp (by fun_prop))

lemma angularCutoff_support {T : ℝ} (hT : 0<T) :
    tsupport (angularCutoff T)⊆{x | x 1∈Icc (-T) T ∧ x 2∈Icc (-T) T} := by
  apply closure_minimal _ ((isClosed_Icc.preimage (continuous_apply 1)).inter
    (isClosed_Icc.preimage (continuous_apply 2)))
  intro x hx
  have ha : periodCutoff T (x 1)≠0 := fun h => hx (by simp [angularCutoff,h])
  have hb : periodCutoff T (x 2)≠0 := fun h => hx (by simp [angularCutoff,h])
  exact ⟨periodCutoff_support hT (subset_tsupport _ ha),periodCutoff_support hT (subset_tsupport _ hb)⟩

lemma angularCutoff_finsum {T : ℝ} (hT : 0<T) (x : Coord3) :
    (∑ᶠ n : Fin 2 → ℤ,angularCutoff T (x+angularShift T n))=1 := by
  let a : ℤ → ℝ := fun n => periodCutoff T (x 1+T*n)
  let b : ℤ → ℝ := fun n => periodCutoff T (x 2+T*n)
  have ha : (∑ᶠ n,a n)=1 := periodCutoff_finsum hT _
  have hb : (∑ᶠ n,b n)=1 := periodCutoff_finsum hT _
  have hf : Function.HasFiniteSupport (fun z : ℤ×ℤ => a z.1*b z.2) := by
    apply ((hasFiniteSupport_of_finsum_eq_one ha).prod (hasFiniteSupport_of_finsum_eq_one hb)).subset
    intro z hz
    exact ⟨fun h => hz (by simp [h]),fun h => hz (by simp [h])⟩
  change (∑ᶠ n : Fin 2 → ℤ,a (n 0)*b (n 1))=1
  have he := finsum_comp_equiv (MeasurableEquiv.finTwoArrow (α:=ℤ)).symm.toEquiv
    (f:=fun n : Fin 2 → ℤ => a (n 0)*b (n 1))
  change (∑ᶠ z : ℤ×ℤ,a z.1*b z.2)=(∑ᶠ n : Fin 2 → ℤ,a (n 0)*b (n 1)) at he
  rw [←he,finsum_curry _ hf]
  simp_rw [←mul_finsum,hb,mul_one]
  exact ha

lemma angularCutoff_periodize {T : ℝ} (hT : 0<T) {f : Coord3 → ℝ} (hp : AngularPeriodic T f) :
    angularPeriodize T (fun x => angularCutoff T x*f x)=f := by
  funext x
  unfold angularPeriodize
  have he : (fun n : Fin 2 → ℤ => angularCutoff T (x+angularShift T n)*f (x+angularShift T n))=
      (fun n => angularCutoff T (x+angularShift T n)*f x) := by
    funext n; rw [hp n x]
  rw [he]
  rw [←finsum_mul,angularCutoff_finsum hT,one_mul]

lemma angularCutoff_compact_support {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : tsupport f⊆{x | x 0∈Icc a b}) :
    tsupport (fun x => angularCutoff T x*f x)⊆Icc ![a,-T,-T] ![b,T,T] := by
  intro x hx
  have h0 := hf ((tsupport_mul_subset_right (f:=angularCutoff T) (g:=f)) hx)
  have hθ := angularCutoff_support hT ((tsupport_mul_subset_left (f:=angularCutoff T) (g:=f)) hx)
  constructor <;> intro i <;> fin_cases i
  · exact h0.1
  · exact hθ.1.1
  · exact hθ.2.1
  · exact h0.2
  · exact hθ.1.2
  · exact hθ.2.2

lemma angularCutoff_compact {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : tsupport f⊆{x | x 0∈Icc a b}) :
    HasCompactSupport (fun x => angularCutoff T x*f x) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (angularCutoff_compact_support hT hf)

lemma AngularPeriodic.coordinate_one {T : ℝ} {f : Coord3 → ℝ} (hp : AngularPeriodic T f)
    (t z : ℝ) : Function.Periodic (fun y => f ![t,y,z]) T := by
  intro y
  have hh := hp ![1,0] ![t,y,z]
  have he : ![t,y,z]+angularShift T ![1,0]=![t,y+T,z] := by
    ext i; fin_cases i <;> simp [angularShift]
  rw [he] at hh
  exact hh

lemma AngularPeriodic.coordinate_two {T : ℝ} {f : Coord3 → ℝ} (hp : AngularPeriodic T f)
    (t y : ℝ) : Function.Periodic (fun z => f ![t,y,z]) T := by
  intro z
  have hh := hp ![0,1] ![t,y,z]
  have he : ![t,y,z]+angularShift T ![0,1]=![t,y,z+T] := by
    ext i; fin_cases i <;> simp [angularShift]
  rw [he] at hh
  exact hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularLocalizedMoments
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma continuous_angular_integral {T : ℝ} (hT : 0≤T) {f : Coord3 → ℝ}
    (hf : Continuous f) (t : ℝ) :
    Continuous (fun y => ∫ z in (0:ℝ)..T,f ![t,y,z]) := by
  simp_rw [intervalIntegral.integral_of_le hT,←integral_Icc_eq_integral_Ioc]
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hf.comp (by fun_prop)

lemma integral_coord3_iterated {f : Coord3 → ℝ} (hf : Integrable f) :
    (∫ x,f x)=∫ t,∫ y,∫ z,f ![t,y,z] := by
  have hi : Integrable (fun x : ℝ×(ℝ×ℝ) => f (threeArrow.symm x)) :=
    (threeArrow_volume.symm.integrable_comp hf.aestronglyMeasurable).mpr hf
  rw [←threeArrow_volume.symm.integral_comp' f]
  change (∫ x,f (threeArrow.symm x) ∂volume.prod volume)=_
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with t ht
  change (∫ x,f (threeArrow.symm (t,x)) ∂volume.prod volume)=_
  rw [integral_prod _ ht]
  simp only [threeArrow_symm_apply]

theorem angularCutoff_integral {T a b : ℝ} (hT : 0<T) {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic T f)
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    (∫ x,angularCutoff T x*f x)=∫ t,∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,f ![t,y,z] := by
  have hi : Integrable (fun x => angularCutoff T x*f x) :=
    ((angularCutoff_smooth T).continuous.mul hf).integrable_of_hasCompactSupport
      (angularCutoff_compact hT hs)
  rw [integral_coord3_iterated hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hz (y : ℝ) :
      (∫ z,angularCutoff T ![t,y,z]*f ![t,y,z])=
        periodCutoff T y*(∫ z in (0:ℝ)..T,f ![t,y,z]) := by
    change (∫ z,periodCutoff T y*periodCutoff T z*f ![t,y,z])=_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    congr 1
    exact periodCutoff_integral hT (hf.comp (by fun_prop)) (hp.coordinate_two t y)
  simp_rw [hz]
  apply periodCutoff_integral hT (continuous_angular_integral hT.le hf t)
  intro y
  apply intervalIntegral.integral_congr
  intro z _
  exact hp.coordinate_one t z y

theorem physicalSourceMoment_angularCutoff {T a b : ℝ} (hT : 0<T)
    {u : Coord3 → Fin 2 → ℝ} {r : PhysicalSourcePair}
    (hu : Continuous u) (hur : AngularPeriodic T u)
    (hr : ∀ j,Continuous (r j)) (hrp : ∀ j,AngularPeriodic T (r j))
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc a b}) :
    physicalSourceMoment u (fun j x => angularCutoff T x*r j x)=periodicSourceMoment T u r := by
  have ht : Continuous (fun x => u x 1*r 0 x-u x 0*r 1 x) := by fun_prop
  have htp : AngularPeriodic T (fun x => u x 1*r 0 x-u x 0*r 1 x) := by
    intro n x
    dsimp only
    rw [hur n x,hrp 0 n x,hrp 1 n x]
  have hts : tsupport (fun x => u x 1*r 0 x-u x 0*r 1 x)⊆{x | x 0∈Icc a b} :=
    (tsupport_sub _ _).trans (union_subset
      ((tsupport_mul_subset_right).trans (hrs 0)) ((tsupport_mul_subset_right).trans (hrs 1)))
  ext i
  fin_cases i
  · exact angularCutoff_integral hT (hr 0) (hrp 0) (hrs 0)
  · exact angularCutoff_integral hT (hr 1) (hrp 1) (hrs 1)
  · change (∫ x,u x 1*(angularCutoff T x*r 0 x)-u x 0*(angularCutoff T x*r 1 x))=_
    have he : (fun x => u x 1*(angularCutoff T x*r 0 x)-u x 0*(angularCutoff T x*r 1 x))=
        (fun x => angularCutoff T x*(u x 1*r 0 x-u x 0*r 1 x)) := by funext x; ring
    rw [he]
    exact angularCutoff_integral hT ht htp hts

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem angularPeriodize_uniform_bound {T : ℝ} (hT : 0<T) (R : ℝ) :
    ∃ M : ℕ,0<M ∧ ∀ (f : Coord3 → E) (C : ℝ),0≤C →
      (∀ x,f x≠0 → ‖x‖≤R) → (∀ x,‖f x‖≤C) →
      ∀ x,‖angularPeriodize T f x‖≤M*C := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (2*R/T)
  let s : Finset (Fin 2 → ℤ) := Finset.Icc (fun _ => -(N:ℤ)) (fun _ => (N:ℤ))
  have hs0 : (0 : Fin 2 → ℤ)∈s := by
    simp only [s,Finset.mem_Icc]
    constructor <;> intro i <;> simp
  refine ⟨s.card,Finset.card_pos.mpr ⟨0,hs0⟩,?_⟩
  intro f C hC hf hbound x
  by_cases hn : ∃ n : Fin 2 → ℤ,f (x+angularShift T n)≠0
  · obtain ⟨n0,hn0⟩ := hn
    let e : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) := (Equiv.addRight n0).toEmbedding
    have hsub : Function.support (fun n => f (x+angularShift T n))⊆↑(s.map e) := by
      intro n hn
      have hdiff : angularShift T (n-n0)=(x+angularShift T n)-(x+angularShift T n0) := by
        have ha := angularShift_add T (n-n0) n0
        rw [sub_add_cancel] at ha
        rw [ha]
        abel
      have hnorm : ‖angularShift T (n-n0)‖≤2*R := by
        rw [hdiff]
        exact (norm_sub_le _ _).trans (by linarith [hf _ hn,hf _ hn0])
      have hi (i : Fin 2) : |((n-n0) i:ℝ)|<(N:ℝ) := by
        have hh := (norm_le_pi_norm (angularShift T (n-n0)) i.succ).trans hnorm
        rw [angularShift_succ,Real.norm_eq_abs,abs_mul,abs_of_pos hT] at hh
        exact ((le_div_iff₀ hT).mpr (by simpa only [mul_comm] using hh)).trans_lt hN
      have hin : n-n0∈s := by
        change _∈Finset.Icc _ _
        rw [Finset.mem_Icc]
        constructor <;> intro i
        · exact_mod_cast (abs_lt.mp (hi i)).1.le
        · exact_mod_cast (abs_lt.mp (hi i)).2.le
      exact Finset.mem_map.mpr ⟨n-n0,hin,by simp [e]⟩
    rw [angularPeriodize,finsum_eq_sum_of_support_subset _ hsub]
    calc
      _ ≤ ∑ n∈s.map e,‖f (x+angularShift T n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈s.map e,C := Finset.sum_le_sum (fun n _ => hbound _)
      _ = s.card*C := by simp
  · have hz : (fun n : Fin 2 → ℤ => f (x+angularShift T n))=0 := by
      funext n
      exact not_ne_iff.mp (fun h => hn ⟨n,h⟩)
    rw [angularPeriodize,hz]
    have he : finsum (0 : (Fin 2 → ℤ) → E)=0 := finsum_zero
    rw [he,norm_zero]
    positivity

omit [NormedSpace ℝ E] in
lemma angularPeriodize_axial_support {T a b : ℝ} {f : Coord3 → E}
    (hs : tsupport f⊆{x | x 0∈Icc a b}) :
    tsupport (angularPeriodize T f)⊆{x | x 0∈Icc a b} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 0))
  intro x hx
  by_contra hx0
  apply hx
  unfold angularPeriodize
  have hz : (fun n : Fin 2 → ℤ => f (x+angularShift T n))=0 := by
    funext n
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := hs h
    change (x 0+0)∈Icc a b at hh
    apply hx0
    change x 0∈Icc a b
    simpa only [add_zero] using hh
  rw [hz]
  exact finsum_zero

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothFamilyGlobalCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
lemma SmoothVanishingPairFamily.sum {ι : Type*} [Fintype ι]
    (r : ι → Fin 2 → P×Coord3 → ℝ) {p : P} {W : Set Coord3}
    (hr : ∀ i,SmoothVanishingPairFamily p W (r i)) :
    SmoothVanishingPairFamily p W (∑ i,r i) := by
  classical
  choose K hK hKW hs using fun i => (hr i).2.2
  refine ⟨fun j => ?_,fun j y => ?_,⋃ i,K i,isCompact_iUnion hK,iUnion_subset hKW,?_⟩
  · have he : ((∑ i,r i) j)=(fun x => ∑ i,r i j x) := by
      funext x; simp only [Finset.sum_apply]
    rw [he]
    exact ContDiff.sum (s:=Finset.univ) (fun i _ => (hr i).1 j)
  · simp only [Finset.sum_apply,(fun i => (hr i).2.1 j y),Finset.sum_const_zero]
  · intro q
    have he : (fun j y => (∑ i,r i) j (q,y))=∑ i,(fun j y => r i j (q,y)) := by
      funext j y; simp
    rw [he]
    exact PairSupported.sum _ _ (fun i _ => (hs i q).mono (subset_iUnion K i))

omit [FiniteDimensional ℝ P] in
lemma vanishing_regions_chain
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3} (hUc : IsPreconnected U)
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    (hreg : ∀ O : Set Coord3,IsOpen O → O.Nonempty → O⊆U →
      ∃ x∈O,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    (B C : VanishingCorrectionRegion u p U) :
    Relation.TransGen (fun B C : VanishingCorrectionRegion u p U =>
      ∃ x∈B.region∩C.region,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) B C := by
  have hc : IsPreconnected (⋃ B : VanishingCorrectionRegion u p U,B.region) := hcover.symm ▸ hUc
  have hp := hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty
  apply Relation.TransGen.mono (fun D E hDE => ?_) B C hp
  exact hreg _ (D.region_open.inter E.region_open) hDE (inter_subset_left.trans D.region_subset)

omit [FiniteDimensional ℝ P] in
lemma vanishing_source_finite_split
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3}
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r) :
    ∃ (s : Finset (VanishingCorrectionRegion u p U)) (g : s → Fin 2 → P×Coord3 → ℝ),
      (∀ i,SmoothVanishingPairFamily p i.val.region (g i)) ∧ (∑ i,g i)=r := by
  classical
  obtain ⟨K,hK,hKU,hs⟩ := hr.2.2
  have hcov : K⊆⋃ B : VanishingCorrectionRegion u p U,B.region := hcover.symm ▸ hKU
  obtain ⟨s,hsc⟩ := hK.elim_finite_subcover (fun B : VanishingCorrectionRegion u p U => B.region)
    (fun B => B.region_open) hcov
  have hsc' : K⊆⋃ B : s,B.val.region := by
    intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp (hsc hx)
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hxB⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ Coord3) hK.isClosed (fun B : s => B.val.region)
    (fun B => B.val.region_open) hsc'
  have hsρ (i : s) : HasCompactSupport (ρ i) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,i.val.region_bounded.subset (hρ i)⟩
  let g : s → Fin 2 → P×Coord3 → ℝ := fun i j z => ρ i z.2*r j z
  refine ⟨s,g,?_,?_⟩
  · intro i
    exact ⟨fun j => ((ρ i).contMDiff.contDiff.comp contDiff_snd).mul (hr.1 j),
      fun j y => by simp [g,hr.2.1 j y],tsupport (ρ i),hsρ i,hρ i,
      fun q j => tsupport_mul_subset_left⟩
  · funext j z
    simp only [Finset.sum_apply,g]
    rw [←Finset.sum_mul]
    by_cases hz : z.2∈K
    · have he := ρ.sum_eq_one hz
      rw [finsum_eq_sum_of_fintype] at he
      rw [he,one_mul]
    · have he : r j z=0 := image_eq_zero_of_notMem_tsupport (f:=fun y => r j (z.1,y))
        (fun h => hz (hs z.1 j h))
      rw [he,mul_zero]

theorem global_vanishing_family_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hUc : IsPreconnected U)
    (hcover : (⋃ B : VanishingCorrectionRegion u p U,B.region)=U)
    (hreg : ∀ O : Set Coord3,IsOpen O → O.Nonempty → O⊆U →
      ∃ x∈O,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))=0 →
      BoundedPhysicallyCorrectable (fun y => u (q,y)) U (fun j y => r j (q,y)) ε := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x,hx⟩ := hne
    have hx' : x∈⋃ B : VanishingCorrectionRegion u p U,B.region := hcover.symm ▸ hx
    obtain ⟨B,_⟩ := mem_iUnion.mp hx'
    obtain ⟨s,g,hg,hge⟩ := vanishing_source_finite_split p hcover hr
    choose a ha ham hac using fun i : s => smooth_chain_source_transport hu p
      (vanishing_regions_chain p hUc hcover hreg i.val B) (hg i)
    have hA := SmoothVanishingPairFamily.sum a ha
    let δ : ℝ := ε/(Fintype.card s+1)
    have hδ : 0<δ := div_pos hε (by positivity)
    have hsolve := B.solve (∑ i,a i) hA δ hδ
    filter_upwards [hsolve,Filter.eventually_all.mpr ham,
      Filter.eventually_all.mpr (fun i => hac i δ hδ)] with q solve mom small total
    have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
    have hQ : (fun j y => (∑ i,a i) j (q,y))=∑ i,(fun j y => a i j (q,y)) := by funext j y; simp
    have hG : (∑ i : s,(fun j y => g i j (q,y)))=(fun j y => r j (q,y)) := by
      funext j y
      have he := congrFun (congrFun hge j) (q,y)
      simpa only [Finset.sum_apply] using he
    have hAm : physicalSourceMoment (fun y => u (q,y)) (fun j y => (∑ i,a i) j (q,y))=0 := by
      rw [hQ,physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (ha i).compact q)]
      simp_rw [mom]
      rw [←physicalSourceMoment_sum _ _ huq.continuous (fun i _ => (hg i).compact q),hG,total]
    have hb := solve hAm
    have ht := BoundedPhysicallyCorrectable.sum Finset.univ
      (fun i => (fun j y => g i j (q,y))-(fun j y => a i j (q,y))) (fun _ => δ) huq (fun i _ => small i)
    have h := ht.add huq hb
    rw [Finset.sum_sub_distrib,←hQ,sub_add_cancel,hG] at h
    have he : (∑ _i : s,δ)+δ=ε := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [δ]
      field_simp
    rwa [he] at h
  · apply Filter.Eventually.of_forall
    intro q _
    have hz : (fun j y => r j (q,y))=0 := by
      funext j y
      exact image_eq_zero_of_notMem_tsupport (f:=fun y => r j (q,y)) (fun h => hne ⟨y,hr.supported q j h⟩)
    rw [hz]
    exact BoundedPhysicallyCorrectable.zero hε.le

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SimpleWallGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma realCLM_invertible {L : ℝ →L[ℝ] ℝ} (hL : L 1≠0) : L.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←smul_eq_mul, map_smul,smul_eq_mul,inv_mul_cancel₀ hL]
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    exact inv_mul_cancel₀ hL

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma real_section_hasDeriv {g : E × ℝ → ℝ} (hg : Differentiable ℝ g)
    (p : E) (z : ℝ) : HasDerivAt (fun t => g (p,t)) (wallDerivative g (p,z)) z := by
  simpa only [Function.comp_def,wallDerivative] using
    (hg (p,z)).hasFDerivAt.comp_hasDerivAt z ((hasDerivAt_const z p).prodMk (hasDerivAt_id z))

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_FlattenedWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

theorem exists_flat_parametric_root
    {g : (P×Q)×ℝ → ℝ} (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (p : P) (q : Q) (hz : ∀ y,g ((p,y),0)=0)
    (hne : wallDerivative g ((p,q),0)≠0) :
    ∃ ρ : P×Q → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧
      (∀ y,ρ (p,y)=0) ∧ ∀ᶠ z in 𝓝 (p,q),g (z,ρ z)=0 := by
  let z : P×Q := (p,q)
  have hd : (fderiv ℝ (fun t => g (z,t)) 0) 1≠0 := by
    have he := (real_section_hasDeriv (hg.differentiable (by simp)) z 0).hasFDerivAt.fderiv
    simpa [he,ContinuousLinearMap.toSpanSingleton_apply,z] using hne
  obtain ⟨L,hL⟩ := realCLM_invertible hd
  obtain ⟨Y,hYs,_,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hg z 0 L hL.symm isOpen_univ (mem_univ _)
  have hf (a : P×Q) (t : ℝ) : (Y (a,t)).1=a := by rw [hY]
  have hYt : (z,0)∈Y.target := by
    simpa only [hY,z,hz] using Y.map_source hYs
  let N : Set (P×Q) := {a | (a,(0:ℝ))∈Y.source∩Y.target}
  have hN : IsOpen N := (Y.open_source.inter Y.open_target).preimage (continuous_id.prodMk continuous_const)
  have hzN : z∈N := ⟨hYs,hYt⟩
  let ψ : P×Q → ℝ := fun a => (Y.symm (a,0)).2
  have hψ : ContDiffOn ℝ (↑(⊤:ℕ∞)) ψ N :=
    contDiff_snd.contDiffOn.comp (hinv.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun _ ha => ha.2)) (fun _ _ => mem_univ _)
  have hroot (a : P×Q) (ha : a∈N) : g (a,ψ a)=0 := by
    have he := congrArg Prod.snd (Y.right_inv ha.2)
    rw [hY] at he
    rw [fiberInverse_fst Y hf ha.2] at he
    exact he
  have hflat (y : Q) (hy : (p,y)∈N) : ψ (p,y)=0 := by
    have he := congrArg Prod.snd (Y.left_inv hy.1)
    simpa only [hY,hz,ψ] using he
  let Ω := N∩Metric.ball z 1
  have hΩ : IsOpen Ω := hN.inter Metric.isOpen_ball
  have hzΩ : z∈Ω := ⟨hzN,Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton hΩ
    (Metric.isBounded_ball.subset inter_subset_right) (singleton_subset_iff.mpr hzΩ)
  refine ⟨fun a => χ a*ψ a,?_,?_,?_⟩
  · exact smooth_mul_of_support_in_open hN hψ hχ (hχs.trans inter_subset_left)
  · intro y
    change χ (p,y)*ψ (p,y)=0
    by_cases hh : χ (p,y)=0
    · rw [hh,zero_mul]
    · rw [hflat y (hχs (subset_tsupport χ hh)).1,mul_zero]
  · filter_upwards [hN.mem_nhds hzN,hχone z (mem_singleton z)] with a ha hχa
    simpa only [hχa,one_mul] using hroot a ha

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_RecenteredWallField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma wallDerivative_eq_of_hasDeriv {f : E×ℝ → ℝ} (hf : Differentiable ℝ f)
    {q : E} {z d : ℝ} (hd : HasDerivAt (fun t => f (q,t)) d z) :
    wallDerivative f (q,z)=d := (real_section_hasDeriv hf q z).unique hd

theorem exists_recentered_critical_wall
    {v : P×(E×ℝ) → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P) (q : E)
    (hz : ∀ y,wallDerivative (fun x => v (p,x)) (y,0)=0)
    (hne : wallDerivative (wallDerivative (fun x => v (p,x))) (q,0)≠0) :
    ∃ ρ : P×E → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ρ ∧ (∀ y,ρ (p,y)=0) ∧
      ∃ w : P×(E×ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=v (p,y)) ∧
        (∀ r y,wallDerivative (fun x => w (r,x)) (y,0)=0) ∧
        ∀ᶠ a in 𝓝 (p,q),∀ z,w (a.1,(a.2,z))=v (a.1,(a.2,z+ρ a)) := by
  let d : P×(E×ℝ) → ℝ := fun a => wallDerivative (fun x => v (a.1,x)) a.2
  have hd : ContDiff ℝ (↑(⊤:ℕ∞)) d := wallDerivative_parametric_smooth hv
  let g : (P×E)×ℝ → ℝ := fun a => d (a.1.1,(a.1.2,a.2))
  have hg : ContDiff ℝ (↑(⊤:ℕ∞)) g := hd.comp (contDiff_fst.fst.prodMk
    (contDiff_fst.snd.prodMk contDiff_snd))
  have hgn : wallDerivative g ((p,q),0)≠0 := by
    have he : wallDerivative g ((p,q),0)=wallDerivative (wallDerivative (fun x => v (p,x))) (q,0) := by
      apply wallDerivative_eq_of_hasDeriv (hg.differentiable (by simp))
      exact real_section_hasDeriv ((wallDerivative_smooth
        (hv.comp (contDiff_const.prodMk contDiff_id))).differentiable (by simp)) q 0
    exact he ▸ hne
  obtain ⟨ρ,hρ,hρ0,hroot⟩ := exists_flat_parametric_root hg p q hz hgn
  let a : P×E → ℝ := fun y => g (y,ρ y)
  have ha : ContDiff ℝ (↑(⊤:ℕ∞)) a := hg.comp (contDiff_id.prodMk hρ)
  let R : P×(E×ℝ) → P×(E×ℝ) := fun y => (y.1,(y.2.1,y.2.2+ρ (y.1,y.2.1)))
  have hR : ContDiff ℝ (↑(⊤:ℕ∞)) R := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk (contDiff_snd.snd.add (hρ.comp (contDiff_fst.prodMk contDiff_snd.fst))))
  let w : P×(E×ℝ) → ℝ := fun y => v (R y)-y.2.2*a (y.1,y.2.1)
  have hw : ContDiff ℝ (↑(⊤:ℕ∞)) w :=
    (hv.comp hR).sub (contDiff_snd.snd.mul (ha.comp (contDiff_fst.prodMk contDiff_snd.fst)))
  refine ⟨ρ,hρ,hρ0,w,hw,?_,?_,?_⟩
  · intro y
    simp only [w,R,a,g,d,hρ0,add_zero,hz,mul_zero,sub_zero]
  · intro r y
    apply wallDerivative_eq_of_hasDeriv ((hw.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
    have h1 := (real_section_hasDeriv (g:=fun x : E×ℝ => v (r,x)) ((hv.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp)) y (0+ρ (r,y))).comp 0 ((hasDerivAt_id (0:ℝ)).add_const (ρ (r,y)))
    have h2 := (hasDerivAt_id (0:ℝ)).mul_const (a (r,y))
    simpa only [w,R,Function.comp_def,id_eq,Pi.sub_def,mul_one,one_mul,a,g,d,zero_add,sub_self] using h1.sub h2
  · filter_upwards [hroot] with y hy
    intro z
    simp only [w,R,a,hy,mul_zero,sub_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeWall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma pureWallMode_smooth (σ lam k : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pureWallMode σ lam k) := by
  unfold pureWallMode
  fun_prop

lemma pureWallMode_normalDerivative (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,z)=
      σ*exp (-lam*q.1)*(-sin (k*z)*k) := by
  apply wallDerivative_eq_of_hasDeriv ((pureWallMode_smooth σ lam k).differentiable (by simp))
  simpa only [pureWallMode,mul_one,id_eq] using
    (((hasDerivAt_id z).const_mul k).cos.const_mul (σ*exp (-lam*q.1)))

lemma pureWallMode_normalSecond (σ lam k : ℝ) (q : ℝ×ℝ) (z : ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,z)=
      -(σ*exp (-lam*q.1)*cos (k*z)*k^2) := by
  apply wallDerivative_eq_of_hasDeriv
    ((wallDerivative_smooth (pureWallMode_smooth σ lam k)).differentiable (by simp))
  have h := (((((hasDerivAt_id z).const_mul k).sin.neg).mul_const k).const_mul
    (σ*exp (-lam*q.1)))
  convert! h using 1 <;> first | rfl | (simp only [pureWallMode_normalDerivative,id_eq,Pi.neg_apply] <;> ring)

lemma pureWallMode_wall_value (σ lam k : ℝ) (q : ℝ×ℝ) :
    pureWallMode σ lam k (q,0)=σ*exp (-lam*q.1) := by simp [pureWallMode]

lemma pureWallMode_wall_critical (σ lam k : ℝ) (q : ℝ×ℝ) :
    wallDerivative (pureWallMode σ lam k) (q,0)=0 := by
  simp [pureWallMode_normalDerivative]

lemma pureWallMode_wall_simple {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0) (q : ℝ×ℝ) :
    wallDerivative (wallDerivative (pureWallMode σ lam k)) (q,0)≠0 := by
  rw [pureWallMode_normalSecond]
  simp only [mul_zero,cos_zero,mul_one,neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (pow_ne_zero 2 hk)

lemma sin_ne_zero_of_abs_lt_pi {z : ℝ} (hz : z≠0) (hp : |z|<Real.pi) : sin z≠0 := by
  rcases lt_or_gt_of_ne hz with hn | hpz
  · have h := (sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn) (by linarith [(abs_lt.mp hp).1])).ne'
    simpa only [sin_neg,neg_ne_zero] using h
  · exact (sin_pos_of_pos_of_lt_pi hpz (abs_lt.mp hp).2).ne'

lemma pureWallMode_quotient_nonzero {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (q : ℝ×ℝ) {z : ℝ} (hz : |k*z|<Real.pi) :
    wallQuotient (wallDerivative (pureWallMode σ lam k)) (q,z)≠0 := by
  by_cases h0 : z=0
  · subst z
    rw [wallQuotient_zero]
    exact pureWallMode_wall_simple hσ hk q
  have hd : wallDerivative (pureWallMode σ lam k) (q,z)≠0 := by
    rw [pureWallMode_normalDerivative]
    exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _))
      (mul_ne_zero (neg_ne_zero.mpr (sin_ne_zero_of_abs_lt_pi (mul_ne_zero hk h0) hz)) hk)
  have he := (smooth_wall_division (wallDerivative_smooth (pureWallMode_smooth σ lam k))
    (pureWallMode_wall_critical σ lam k)).2 (q,z)
  exact (mul_ne_zero_iff.mp (he ▸ hd)).2

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeWallRegion
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_pure_mode_wall_region
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hbase : ∀ y,v (p,y)=pureWallMode σ lam k y)
    {W : Set Coord3} (hW : IsOpen W) {x : Coord3} (hx : x∈W) (hxz : x 2=0) :
    ∃ B : VanishingCorrectionRegion (fun z => wallCoordinatePair (fun y => v (z.1,y)) z.2) p W,
      x∈B.region := by
  have hstrip : IsOpen {y : Coord3 | |k*y 2|<Real.pi} :=
    isOpen_lt (continuous_const.mul (continuous_apply 2)).abs continuous_const
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hW.inter hstrip) x
    ⟨hx,by simp only [mem_ofPred_eq,hxz,mul_zero,abs_zero]; exact Real.pi_pos⟩
  let U := Metric.ball x δ
  have hproj : ∀ y∈U,boxCoordinates.symm ((boxCoordinates y).1,0)∈U := by
    intro y hy
    rw [Metric.mem_ball,dist_pi_lt_iff hδ] at hy ⊢
    intro i
    fin_cases i
    · exact hy 0
    · exact hy 1
    · change dist (0:ℝ) (x 2)<δ
      simpa only [hxz,dist_self] using hδ
  have hrect : ∀ z∈Icc (x 0-δ/2) (x 0+δ/2)×ˢIcc (x 1-δ/2) (x 1+δ/2),
      boxCoordinates.symm (z,0)∈U := by
    intro z hz
    rw [Metric.mem_ball,dist_pi_lt_iff hδ]
    intro i
    fin_cases i
    · change dist z.1 (x 0)<δ
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.1.1,hz.1.2]
    · change dist z.2 (x 1)<δ
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.2.1,hz.2.2]
    · change dist (0:ℝ) (x 2)<δ
      simpa only [hxz,dist_self] using hδ
  have hcp : Convex ℝ {y : Coord3 | 0<y 2} :=
    convex_halfSpace_gt ⟨fun _ _ => rfl,fun _ _ => rfl⟩ 0
  have hcn : Convex ℝ {y : Coord3 | y 2<0} :=
    convex_halfSpace_lt ⟨fun _ _ => rfl,fun _ _ => rfl⟩ 0
  have hnb : ∀ y∈U,wallQuotient (wallDerivative (fun z => v (p,z))) (boxCoordinates y)≠0 := by
    intro y hy
    rw [show (fun z => v (p,z))=pureWallMode σ lam k from funext hbase]
    exact pureWallMode_quotient_nonzero hσ hk _ (hball hy).2
  let B := criticalWallRegion hv p hz Metric.isOpen_ball Metric.isBounded_ball
    (fun y hy => (hball hy).1) (Metric.nonempty_ball.mpr hδ)
    (((convex_ball x δ).inter hcp).isPreconnected)
    (((convex_ball x δ).inter hcn).isPreconnected) hproj hnb
    (show x 0-δ/2<x 0+δ/2 by linarith)
    (show x 1-δ/2<x 1+δ/2 by linarith) hσ hlam hrect
    (fun z => (hbase (z,0)).trans (pureWallMode_wall_value σ lam k z))
  exact ⟨B,Metric.mem_ball_self hδ⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_LocalFamilyRegionCoordinates
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_transported_vanishing_region
    {u v : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {U : Set Coord3} (hYU : Y.source⊆univ×ˢU)
    {x : Coord3} (hx : (p,x)∈Y.source)
    (hpot : ∀ z∈Y.source,v (z.1,(Y z).2)=u z)
    (hlocal : ∀ A : Set Coord3,IsOpen A → (Y (p,x)).2∈A →
      ∃ B : VanishingCorrectionRegion v p A,(Y (p,x)).2∈B.region) :
    ∃ B : VanishingCorrectionRegion u p U,x∈B.region := by
  let z := (Y (p,x)).2
  have hpz : (p,z)∈Y.target := by
    have he : (p,z)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he]
    exact Y.map_source hx
  obtain ⟨V₀,A₀,hV₀,hA₀,hp₀,hz₀,hprod₀⟩ := exists_open_product_inside Y.open_target hpz
  obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hV₀ p hp₀
  obtain ⟨η,hη,hηball⟩ := Metric.isOpen_iff.mp hA₀ z hz₀
  let Kp := Metric.closedBall p (δ/2)
  let Ka := Metric.closedBall z (η/2)
  let A := Metric.ball z (η/2)
  have hpK : Kp⊆V₀ := fun q hq => hδball
    (lt_of_le_of_lt hq (by linarith : δ/2<δ))
  have haK : Ka⊆A₀ := fun y hy => hηball
    (lt_of_le_of_lt hy (by linarith : η/2<η))
  have hjoint : Kp×ˢKa⊆Y.target := fun q hq => hprod₀ ⟨hpK hq.1,haK hq.2⟩
  obtain ⟨C,hC,hbound⟩ := parametric_chart_compact_bounds Y hY hsm hinv
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) hjoint
  obtain ⟨B,hzB⟩ := hlocal A Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
  obtain ⟨τ,hτ,hτball⟩ := Metric.isOpen_iff.mp B.region_open z hzB
  let K := Metric.closedBall z (τ/2)
  have hKB : K⊆B.region := fun y hy => hτball
    (lt_of_le_of_lt hy (by linarith : τ/2<τ))
  let O : Set (P×Coord3) := Y.source∩{q | (Y q).2∈Metric.ball z (τ/2)}
  have hO : IsOpen O := Y.open_source.inter
    (Metric.isOpen_ball.preimage (continuous_snd.comp hsm.continuous))
  have hxO : (p,x)∈O := ⟨hx,Metric.mem_ball_self (by positivity)⟩
  obtain ⟨V₁,W₁,hV₁,hW₁,hp₁,hx₁,hprod₁⟩ := exists_open_product_inside hO hxO
  let V := Metric.ball p (δ/2)∩V₁
  let W := W₁∩Metric.ball x 1
  have hVp : p∈V := ⟨Metric.mem_ball_self (by positivity),hp₁⟩
  have hWx : x∈W := ⟨hx₁,Metric.mem_ball_self zero_lt_one⟩
  have hWU : W⊆U := fun y hy => (hYU (hprod₁ (show (p,y)∈V₁×ˢW₁ from ⟨hp₁,hy.1⟩)).1).2
  have hVA : V×ˢA⊆Y.target := fun q hq => hjoint
    ⟨Metric.ball_subset_closedBall hq.1.1,Metric.ball_subset_closedBall hq.2⟩
  have hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K := by
    intro q hq y hy
    have hh := hprod₁ (show (q,y)∈V₁×ˢW₁ from ⟨hq.2,hy.1⟩)
    exact ⟨(Y (q,y)).2,Metric.ball_subset_closedBall hh.2,(fiberSlice Y hY q).left_inv hh.1⟩
  have himage : ∀ q∈V,(fiberSlice Y hY q).symm '' A⊆U := by
    rintro q hq _ ⟨y,hy,rfl⟩
    exact (hYU ((fiberSlice Y hY q).map_target (hVA ⟨hq,hy⟩))).2
  have hpot' : ∀ q∈V,∀ y∈A,u (q,(fiberSlice Y hY q).symm y)=v (q,y) := by
    intro q hq y hy
    have hyt := hVA (show (q,y)∈V×ˢA from ⟨hq,hy⟩)
    have hys := (fiberSlice Y hY q).map_target hyt
    have hh := hpot (q,(fiberSlice Y hY q).symm y) hys
    rw [show (Y (q,(fiberSlice Y hY q).symm y)).2=y from
      (fiberSlice Y hY q).right_inv hyt] at hh
    exact hh.symm
  let D := VanishingCorrectionRegion.piola hu hv p Y hY hsm hinv
    (Metric.isOpen_ball.inter hV₁) hVp (Metric.isBounded_ball.subset inter_subset_left)
    Metric.isOpen_ball B (isCompact_closedBall _ _) hKB hVA hW
    (hW₁.inter Metric.isOpen_ball) ⟨x,hWx⟩
    (Metric.isBounded_ball.subset inter_subset_right) hWU himage hpot' hC
    (fun q hq y hy => (hbound (q,y)
      ⟨Metric.ball_subset_closedBall hq.1,Metric.ball_subset_closedBall hy⟩).2.2.2)
  exact ⟨D,hWx⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ParametricAxialNormalization
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_axial_normalization
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P) (x : Coord3)
    {V : Coord3 → ℝ} (hV : ContDiff ℝ (↑(⊤:ℕ∞)) V)
    (hub : ∀ y,u (p,y)=y 0) (hvb : ∀ y,v (p,y)=V y) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ (∀ q y,Y (q,y)=(q,![u (q,y),y 1,y 2])) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target ∧
      ∃ w : P×Coord3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=V y) ∧ ∀ᶠ z in 𝓝 (p,x),w (Y z)=v z := by
  let φ : P×Coord3 → Coord3 := fun q => ![u q,q.2 1,q.2 2]
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact hu
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => q.2 1)
      exact (contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q : P×Coord3 => q.2 2)
      exact (contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd
  have hφbase (y : Coord3) : φ (p,y)=y := by
    ext i
    fin_cases i <;> simp [φ,hub]
  have hφd : fderiv ℝ (fun y => φ (p,y)) x=(ContinuousLinearEquiv.refl ℝ Coord3 : Coord3 →L[ℝ] Coord3) := by
    rw [show (fun y => φ (p,y))=id from funext hφbase,fderiv_id]
    rfl
  obtain ⟨Y,hYs,_,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hφ p x
    (ContinuousLinearEquiv.refl ℝ Coord3) hφd isOpen_univ (mem_univ _)
  have hbase (y : Coord3) : Y (p,y)=(p,y) := by rw [hY,hφbase]
  have hYt : (p,x)∈Y.target := by simpa only [hbase] using Y.map_source hYs
  let N := Y.source∩Y.target
  have hN : IsOpen N := Y.open_source.inter Y.open_target
  have hpN : (p,x)∈N := ⟨hYs,hYt⟩
  let Ω := N∩Metric.ball (p,x) 1
  have hΩ : IsOpen Ω := hN.inter Metric.isOpen_ball
  have hpΩ : (p,x)∈Ω := ⟨hpN,Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton hΩ
    (Metric.isBounded_ball.subset inter_subset_right) (singleton_subset_iff.mpr hpΩ)
  let f : P×Coord3 → ℝ := fun z => v (Y.symm z)-V z.2
  have hf : ContDiffOn ℝ (↑(⊤:ℕ∞)) f N :=
    (hv.contDiffOn.comp (hinv.mono inter_subset_right) (fun _ _ => mem_univ _)).sub
      (hV.comp contDiff_snd).contDiffOn
  let w : P×Coord3 → ℝ := fun z => V z.2+χ z*f z
  have hw : ContDiff ℝ (↑(⊤:ℕ∞)) w :=
    (hV.comp contDiff_snd).add (smooth_mul_of_support_in_open hN hf hχ (hχs.trans inter_subset_left))
  refine ⟨Y,hYs,hY,hsm,hinv,w,hw,?_,?_⟩
  · intro y
    by_cases hc : χ (p,y)=0
    · simp only [w,hc,zero_mul,add_zero]
    · have he : Y.symm (p,y)=(p,y) := by
        simpa only [hbase] using Y.left_inv (hχs (subset_tsupport χ hc)).1.1
      simp only [w,f,he,hvb,sub_self,mul_zero,add_zero]
  · have hh : Tendsto Y (𝓝 (p,x)) (𝓝 (p,x)) := by
      simpa only [hbase] using hsm.continuous.tendsto (p,x)
    filter_upwards [Y.open_source.mem_nhds hYs,hh.eventually (hχone (p,x) (mem_singleton _))]
      with z hz hχz
    simp only [w,f,hχz,one_mul,Y.left_inv hz,add_sub_cancel]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SimpleCriticalWallCoordinates
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_simple_critical_wall_coordinates
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (_ : x 2=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3),
      (p,x)∈Y.source ∧ Y.source⊆univ×ˢU ∧
      (∀ q y,(Y (q,y)).1=q) ∧ (∀ y,Y (p,y)=(p,y)) ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) Y ∧ ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target ∧
      ∃ w : P×Box3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) w ∧
        (∀ y,w (p,y)=pureWallMode σ lam k y) ∧
        (∀ q z,wallDerivative (fun y => w (q,y)) (z,0)=0) ∧
        ∀ z∈Y.source,wallCoordinatePair (fun y => w (z.1,y)) (Y z).2=![u z,v z] := by
  let V : Coord3 → ℝ := pureWallMode σ lam k∘boxCoordinates
  have hVs : ContDiff ℝ (↑(⊤:ℕ∞)) V := (pureWallMode_smooth σ lam k).comp boxCoordinates.contDiff
  obtain ⟨A,hAs,hA,hAsm,hAi,w₀,hw₀,hw₀b,hw₀e⟩ :=
    exists_parametric_axial_normalization hu hv p x hVs hub hvb
  let wB : P×Box3 → ℝ := fun z => w₀ (z.1,boxCoordinates.symm z.2)
  have hwB : ContDiff ℝ (↑(⊤:ℕ∞)) wB :=
    hw₀.comp (contDiff_fst.prodMk (boxCoordinates.symm.contDiff.comp contDiff_snd))
  have hwBb : (fun y => wB (p,y))=pureWallMode σ lam k := by
    funext y
    simp only [wB,hw₀b,V,Function.comp_apply,boxCoordinates.apply_symm_apply]
  have hwBz : ∀ y,wallDerivative (fun z => wB (p,z)) (y,0)=0 := by
    rw [hwBb]; exact pureWallMode_wall_critical σ lam k
  have hwBn : wallDerivative (wallDerivative (fun z => wB (p,z))) ((x 0,x 1),0)≠0 := by
    rw [hwBb]; exact pureWallMode_wall_simple hσ hk _
  obtain ⟨ρ,hρ,hρ₀,w,hw,hwb,hwz,hwe⟩ := exists_recentered_critical_wall hwB p (x 0,x 1) hwBz hwBn
  let Q : P×Coord3 → P×(ℝ×ℝ) := fun z => (z.1,(u z,z.2 1))
  have hQ : ContDiff ℝ (↑(⊤:ℕ∞)) Q := contDiff_fst.prodMk
    (hu.prodMk ((contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd))
  let φ : P×Coord3 → Coord3 := fun z => ![u z,z.2 1,z.2 2-ρ (Q z)]
  have hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ (↑(⊤:ℕ∞)) u
      exact hu
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => z.2 1)
      exact (contDiff_apply ℝ ℝ (1:Fin 3)).comp contDiff_snd
    · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => z.2 2-ρ (Q z))
      exact ((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).sub (hρ.comp hQ)
  have hφb (y : Coord3) : φ (p,y)=y := by
    ext i
    fin_cases i <;> simp [φ,Q,hub,hρ₀]
  have hQt : Tendsto Q (𝓝 (p,x)) (𝓝 (p,(x 0,x 1))) := by
    simpa only [Q,hub] using hQ.continuous.tendsto (p,x)
  have he : ∀ᶠ z in 𝓝 (p,x),wallCoordinatePair (fun y => w (z.1,y)) (φ z)=![u z,v z] := by
    filter_upwards [hw₀e,hQt.eventually hwe] with z haz hwz'
    ext i
    fin_cases i
    · rfl
    · change w (z.1,((u z,z.2 1),z.2 2-ρ (Q z)))=v z
      rw [hwz' (z.2 2-ρ (Q z))]
      simp only [Q,sub_add_cancel,wB]
      change w₀ (z.1,![u z,z.2 1,z.2 2])=v z
      simpa only [hA] using haz
  obtain ⟨N,hN,hNo,hpN⟩ := mem_nhds_iff.mp he
  have hL : fderiv ℝ (fun y => φ (p,y)) x=(ContinuousLinearEquiv.refl ℝ Coord3 : Coord3 →L[ℝ] Coord3) := by
    rw [show (fun y => φ (p,y))=id from funext hφb,fderiv_id]
    rfl
  obtain ⟨Y,hYs,hYN,hY,hsm,hinv⟩ := exists_parametric_diffeomorph hφ p x
    (ContinuousLinearEquiv.refl ℝ Coord3) hL (hNo.inter (isOpen_univ.prod hU)) ⟨hpN,mem_univ p,hx⟩
  refine ⟨Y,hYs,fun z hz => (hYN hz).2,fun q y => by simp only [hY],
    fun y => by rw [hY,hφb],hsm,hinv,w,hw,?_,hwz,?_⟩
  · intro y
    exact (hwb y).trans (congrFun hwBb y)
  · intro z hz
    rw [hY]
    exact hN (hYN hz).1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SimpleCriticalWallRegion
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_simple_critical_wall_region
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (hxz : x 2=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ B : VanishingCorrectionRegion (fun z => ![u z,v z]) p U,x∈B.region := by
  obtain ⟨Y,hYs,hYU,hY,hYb,hsm,hinv,w,hw,hwb,hwz,hpot⟩ :=
    exists_simple_critical_wall_coordinates hu hv p hσ hk hub hvb hxz hU hx
  have huv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![u z,v z]) :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  apply exists_transported_vanishing_region huv (wallCoordinatePair_parametric_smooth hw)
    p Y hY hsm hinv hYU hYs hpot
  intro A hA hxA
  rw [hYb] at hxA ⊢
  exact exists_pure_mode_wall_region hw p hwz hσ hlam hk hwb hA hxA hxz

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PureModeFamilyLocalCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma pureWallMode_shift_wall {σ lam k a : ℝ} (ha : sin (k*a)=0) (y : Coord3) :
    pureWallMode σ lam k (boxCoordinates (y+![0,0,a]))=
      pureWallMode (σ*cos (k*a)) lam k (boxCoordinates y) := by
  change σ*exp (-lam*(y 0+0))*cos (k*(y 2+a))=
    (σ*cos (k*a))*exp (-lam*y 0)*cos (k*y 2)
  rw [add_zero,mul_add,cos_add,ha,mul_zero,sub_zero]
  ring

theorem exists_pure_mode_critical_family_region
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {x : Coord3} (hxz : sin (k*x 2)=0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    ∃ B : VanishingCorrectionRegion (fun z => ![u z,v z]) p U,x∈B.region := by
  let a : Coord3 := ![0,0,x 2]
  let τ : P×Coord3 → P×Coord3 := fun z => (z.1,z.2+a)
  have hτ : ContDiff ℝ (↑(⊤:ℕ∞)) τ := contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  let ut := u∘τ
  let vt := v∘τ
  have hut : ∀ y,ut (p,y)=y 0 := by
    intro y
    change u (p,y+a)=y 0
    rw [hub]
    change y 0+0=y 0
    exact add_zero _
  have hvt : ∀ y,vt (p,y)=pureWallMode (σ*cos (k*x 2)) lam k (boxCoordinates y) := by
    intro y
    exact (hvb (y+a)).trans (pureWallMode_shift_wall hxz y)
  have hcos : cos (k*x 2)≠0 := by
    intro h
    have hh := sin_sq_add_cos_sq (k*x 2)
    rw [hxz,h] at hh
    norm_num at hh
  let Y₀ := ((Homeomorph.refl P).prodCongr (Homeomorph.subRight a)).toOpenPartialHomeomorph
  let Y := Y₀.restr (univ×ˢU)
  have hYs : Y.source=univ×ˢU := by
    simp only [Y,OpenPartialHomeomorph.restr_source,(isOpen_univ.prod hU).interior_eq]
    exact univ_inter _
  have hY : ∀ q y,(Y (q,y)).1=q := fun _ _ => rfl
  have hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y := contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)
  have hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target :=
    (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn
  have hpot : ∀ z∈Y.source,![ut (z.1,(Y z).2),vt (z.1,(Y z).2)]=![u z,v z] := by
    intro z _
    change ![u (z.1,z.2-a+a),v (z.1,z.2-a+a)]=![u z,v z]
    rw [sub_add_cancel]
  have huv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![u z,v z]) :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  have htv : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => ![ut z,vt z]) := huv.comp hτ
  apply exists_transported_vanishing_region huv htv p Y hY hsm hinv
    (hYs ▸ Subset.rfl) (hYs ▸ (show (p,x)∈univ×ˢU from ⟨mem_univ _,hx⟩)) hpot
  intro A hA hxA
  apply exists_simple_critical_wall_region (hu.comp hτ) (hv.comp hτ) p
    (mul_ne_zero hσ hcos) hlam hk hut hvt (x := x-a) (by simp [a]) hA hxA

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma pureWallMode_pair_regular {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    {x : Coord3} (hx : sin (k*x 2)≠0) :
    Function.Surjective (fderiv ℝ (wallCoordinatePair (pureWallMode σ lam k)) x) := by
  apply wallCoordinatePair_surjective ((pureWallMode_smooth σ lam k).differentiable (by simp))
  rw [pureWallMode_normalDerivative]
  exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (mul_ne_zero (neg_ne_zero.mpr hx) hk)

lemma exists_sin_ne_zero_in_open {k : ℝ} (hk : k≠0)
    {O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ x∈O,sin (k*x 2)≠0 := by
  obtain ⟨x,hx⟩ := hne
  by_cases hs : sin (k*x 2)=0
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO x hx
    let δ := min ε (Real.pi/|k|)/2
    have hak : 0 < |k| := abs_pos.mpr hk
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hδε : δ<ε := by dsimp [δ]; linarith [min_le_left ε (Real.pi/|k|)]
    have hδpi : δ<Real.pi/|k| := by
      dsimp [δ]
      linarith [min_le_right ε (Real.pi/|k|),div_pos Real.pi_pos hak]
    let y : Coord3 := x+![0,0,δ]
    have hy : y∈O := by
      apply hball
      rw [Metric.mem_ball,dist_pi_lt_iff hε]
      intro i
      fin_cases i
      · change dist (x 0+0) (x 0)<ε
        simpa only [add_zero,dist_self] using hε
      · change dist (x 1+0) (x 1)<ε
        simpa only [add_zero,dist_self] using hε
      · change dist (x 2+δ) (x 2)<ε
        simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hδ] using hδε
    have hcos : cos (k*x 2)≠0 := by
      intro h
      have hh := sin_sq_add_cos_sq (k*x 2)
      rw [hs,h] at hh
      norm_num at hh
    refine ⟨y,hy,?_⟩
    change sin (k*(x 2+δ))≠0
    rw [mul_add,sin_add,hs,zero_mul,zero_add]
    apply mul_ne_zero hcos
    apply sin_ne_zero_of_abs_lt_pi (mul_ne_zero hk hδ.ne')
    rw [abs_mul,abs_of_pos hδ]
    simpa only [mul_comm] using (lt_div_iff₀ hak).mp hδpi
  · exact ⟨x,hx,hs⟩

theorem pure_mode_family_correction
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    {U : Set Coord3} (hU : IsOpen U) (hUc : IsPreconnected U)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p U r)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => ![u (q,y),v (q,y)]) (fun j y => r j (q,y))=0 →
      BoundedPhysicallyCorrectable (fun y => ![u (q,y),v (q,y)]) U (fun j y => r j (q,y)) ε := by
  let F : P×Coord3 → Fin 2 → ℝ := fun z => ![u z,v z]
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) F :=
    contDiff_pi.mpr (by intro i; fin_cases i; exact hu; exact hv)
  have hFb : (fun y => F (p,y))=wallCoordinatePair (pureWallMode σ lam k) := by
    funext y j
    fin_cases j
    · exact hub y
    · exact hvb y
  have hreg {y : Coord3} (hy : sin (k*y 2)≠0) :
      Function.Surjective (fderiv ℝ (fun y => F (p,y)) y) := by
    rw [hFb]
    exact pureWallMode_pair_regular hσ hk hy
  have hcover : (⋃ B : VanishingCorrectionRegion F p U,B.region)=U := by
    apply Subset.antisymm (iUnion_subset (fun B => B.region_subset))
    intro x hx
    by_cases hs : sin (k*x 2)=0
    · obtain ⟨B,hB⟩ := exists_pure_mode_critical_family_region hu hv p hσ hlam hk hub hvb hs hU hx
      exact mem_iUnion.mpr ⟨B,hB⟩
    · obtain ⟨B,hB⟩ := exists_parametric_correction_box hF p hU hx (hreg hs)
      exact mem_iUnion.mpr ⟨B.toVanishing p,hB⟩
  apply global_vanishing_family_correction hF p hUc hcover ?_ hr hε
  intro O hO hne _
  obtain ⟨x,hx,hs⟩ := exists_sin_ne_zero_in_open hk hO hne
  exact ⟨x,hx,hreg hs⟩

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PeriodicFamilyCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma correctionBox_convex (a b : Coord3) : Convex ℝ (correctionBox a b) := by
  have he : correctionBox a b=Set.univ.pi (fun i => Ioo (a i) (b i)) := by
    ext x
    simp only [mem_correctionBox,Set.mem_pi,mem_univ,true_implies,mem_Ioo]
  rw [he]
  exact convex_pi (fun _ _ => convex_Ioo _ _)

theorem periodic_pure_mode_family_correction
    {u v : P×Coord3 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    {σ lam k T l a b d : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0) (hT : 0<T)
    (hla : l<a) (hbd : b<d)
    (hub : ∀ y,u (p,y)=y 0)
    (hvb : ∀ y,v (p,y)=pureWallMode σ lam k (boxCoordinates y))
    (hup : ∀ q,AngularPeriodic T (fun y => ![u (q,y),v (q,y)]))
    {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j))
    (hrz : ∀ j x,r j (p,x)=0)
    (hrp : ∀ j q,AngularPeriodic T (fun x => r j (q,x)))
    (hrs : ∀ j q,tsupport (fun x => r j (q,x))⊆{x | x 0∈Icc a b})
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,periodicSourceMoment T (fun y => ![u (q,y),v (q,y)]) (fun j y => r j (q,y))=0 →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic T H ∧
        tsupport H⊆{x | x 0∈Icc l d} ∧ (∀ x,(H x).IsSymm) ∧
        (∀ j,symmetricSource H (fun y => ![u (q,y),v (q,y)]) j=(fun y => r j (q,y))) ∧
        ∀ x,‖H x‖≤ε := by
  let L : Coord3 := ![l,-T-1,-T-1]
  let D : Coord3 := ![d,T+1,T+1]
  let U := correctionBox L D
  let K : Set Coord3 := Icc ![a,-T,-T] ![b,T,T]
  let R : Fin 2 → P×Coord3 → ℝ := fun j z => angularCutoff T z.2*r j z
  have hKU : K⊆U := by
    intro x hx
    apply mem_correctionBox.mpr
    intro i
    fin_cases i
    · exact ⟨hla.trans_le (hx.1 0),(hx.2 0).trans_lt hbd⟩
    · have h1 : -T≤x 1 ∧ x 1≤T := ⟨hx.1 1,hx.2 1⟩
      constructor <;> dsimp [L,D] <;> linarith [h1.1,h1.2]
    · have h2 : -T≤x 2 ∧ x 2≤T := ⟨hx.1 2,hx.2 2⟩
      constructor <;> dsimp [L,D] <;> linarith [h2.1,h2.2]
  have hR : SmoothVanishingPairFamily p U R := by
    refine ⟨fun j => ((angularCutoff_smooth T).comp contDiff_snd).mul (hr j),?_,K,isCompact_Icc,hKU,?_⟩
    · intro j x
      dsimp [R]
      rw [hrz,mul_zero]
    · intro q j
      exact angularCutoff_compact_support hT (hrs j q)
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc L D)).isBounded.exists_norm_le
  obtain ⟨M,hM,hMp⟩ := angularPeriodize_uniform_bound (E:=Mat3) hT B
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hεM : 0<ε/M := div_pos hε hMr
  have hc := pure_mode_family_correction hu hv p hσ hlam hk hub hvb
    (correctionBox_isOpen L D) (correctionBox_convex L D).isPreconnected hR hεM
  filter_upwards [hc] with q hq
  intro hm
  have hF : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => ![u (q,y),v (q,y)]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact hu.comp (contDiff_const.prodMk contDiff_id)
    · exact hv.comp (contDiff_const.prodMk contDiff_id)
  have hmo : physicalSourceMoment (fun y => ![u (q,y),v (q,y)]) (fun j y => R j (q,y))=0 := by
    exact (physicalSourceMoment_angularCutoff (r:=fun j x => r j (q,x)) hT hF.continuous (hup q)
      (fun j => ((hr j).comp (contDiff_const.prodMk contDiff_id)).continuous)
      (fun j => hrp j q) (fun j => hrs j q)).trans hm
  obtain ⟨H,hH,hHc,hHs,hHsy,hHr,hHb⟩ := hq hmo
  have hnorm : ∀ x,H x≠0 → ‖x‖≤B := by
    intro x hx
    apply hB x
    have hh := mem_correctionBox.mp (hHs (subset_tsupport H hx))
    exact ⟨fun i => (hh i).1.le,fun i => (hh i).2.le⟩
  have hax : tsupport H⊆{x | x 0∈Icc l d} := by
    intro x hx
    have hh := mem_correctionBox.mp (hHs hx) 0
    exact ⟨hh.1.le,hh.2.le⟩
  refine ⟨angularPeriodize T H,angularPeriodize_smooth hT hH hHc,
    angularPeriodize_periodic T H,angularPeriodize_axial_support hax,
    angularPeriodize_symmetric hT hHc hHsy,?_,?_⟩
  · intro j
    funext x
    rw [symmetricSource_angularPeriodize hT hH hHc hF (hup q),hHr j]
    exact congrFun (angularCutoff_periodize hT (hrp j q)) x
  · intro x
    have hh := hMp H (ε/M) hεM.le hnorm hHb x
    have he : (M:ℝ)*(ε/M)=ε := by field_simp
    rwa [he] at hh

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma flatPhaseMode_angularPeriodic (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) (phase : ℝ) :
    AngularPeriodic (2*Real.pi) (flatPhaseMode s h phase) := by
  intro n x
  have he : torusAngular h (x+angularShift (2*Real.pi) n)+phase=
      torusAngular h x+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi) := by
    change (h 0:ℝ)*(x 1+2*Real.pi*(n 0:ℝ))+(h 1:ℝ)*(x 2+2*Real.pi*(n 1:ℝ))+phase=
      (h 0:ℝ)*x 1+(h 1:ℝ)*x 2+phase+(h 0*n 0+h 1*n 1:ℤ)*(2*Real.pi)
    push_cast
    ring
  change exp (-torusRate s h*(x 0+0))*cos (torusAngular h (x+angularShift (2*Real.pi) n)+phase)=_
  rw [add_zero,he,cos_add_int_mul_two_pi]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_FlatBackgroundTensor
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma flatBackgroundTensor_flux {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : Differentiable ℝ u) (j : Fin 2) (x : Coord3) :
    (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j=
      flatModeFlux s (fun y => u y j) x := by
  have hd (i : Fin 3) : gradientColumns (fderiv ℝ u x) i j=
      fderiv ℝ (fun y => u y j) x (flatAxis i) := by
    rw [potential_component_fderiv hu]
    rfl
  ext i
  fin_cases i <;>
    simp [Matrix.col_apply,Fin.sum_univ_three,hd,flatBackgroundTensor,
      flatModeFlux,Fin.reduceFinMk,Matrix.vecMul,dotProduct]

lemma flatBackgroundTensor_source {s : Fin 3→ℝ} {u : Coord3→Fin 2→ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) (x : Coord3) :
    symmetricSource (fun _ => flatBackgroundTensor s) u j x=
      flatTensorLaplacian s (fun y => u y j) x := by
  have he : (fun x => (flatBackgroundTensor s*gradientColumns (fderiv ℝ u x)).col j)=
      flatModeFlux s (fun y => u y j) := funext (flatBackgroundTensor_flux (hu.differentiable (by simp)) j)
  unfold symmetricSource
  rw [he,flatModeFlux_divergence (((contDiff_pi.mp hu) j).contDiffAt)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AffineFourierField
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma axial_affine_fderiv (α β : ℝ) (x : Coord3) :
    fderiv ℝ (fun y : Coord3 => α*y 0+β) x=α • ContinuousLinearMap.proj 0 := by
  have hh := (((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x)).const_mul α).add_const β
  exact hh.fderiv

lemma flatTensorLaplacian_axial_affine (s : Fin 3→ℝ) (α β : ℝ) (x : Coord3) :
    flatTensorLaplacian s (fun y => α*y 0+β) x=0 := by
  have he : fderiv ℝ (fun y : Coord3 => α*y 0+β)=fun _ => α • ContinuousLinearMap.proj 0 :=
    funext (axial_affine_fderiv α β)
  unfold flatTensorLaplacian flatTensorLaplacianCLM
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousMultilinearMap.apply_apply,smul_eq_mul,iteratedFDeriv_two_apply,he,
    fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,mul_zero,add_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierPairFlux
attribute [-instance] _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma pureWallMode_eq_flatPhaseMode (s : Fin 3 → ℝ) (k : ℤ) (x : Coord3) :
    pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x)=flatPhaseMode s ![0,k] 0 x := by
  simp [pureWallMode,flatPhaseMode,torusAngular,boxCoordinates_apply]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingInterpolation
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma fourierMatchingCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) fourierMatchingCutoff :=
  contDiff_const.sub (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const 2))

lemma fourierMatchingPair_smooth (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fourierMatchingPair s k f g) := by
  have ht : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ×Coord3 => z.2 0) :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact ht.add ((fourierMatchingCutoff_smooth.comp ht).mul hf)
  · exact ((flatPhaseMode_smooth s ![0,k] 0).comp contDiff_snd).add
      ((fourierMatchingCutoff_smooth.comp ht).mul hg)

lemma fourierMatchingPair_periodic (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hg : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) (p : ℝ) :
    AngularPeriodic (2*Real.pi) (fun x => fourierMatchingPair s k f g (p,x)) := by
  intro n x
  dsimp only [fourierMatchingPair]
  have hfe : f (p,x+angularShift (2*Real.pi) n)=f (p,x) := hf p n x
  have hge : g (p,x+angularShift (2*Real.pi) n)=g (p,x) := hg p n x
  rw [hfe,hge,flatPhaseMode_angularPeriodic s ![0,k] 0 n x]
  have he : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  rw [he]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma fourierResidualCutoff_smooth : ContDiff ℝ (↑(⊤:ℕ∞)) fourierResidualCutoff :=
  (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
lemma fourierResidualCutoff_zero_left {t : ℝ} (ht : t≤1) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (by linarith),zero_mul]
lemma fourierResidualCutoff_zero_right {t : ℝ} (ht : 5≤t) : fourierResidualCutoff t=0 := by
  rw [fourierResidualCutoff,smoothTransition.zero_of_nonpos (show 5-t≤0 by linarith),mul_zero]

lemma fourierMatchingResidual_smooth (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤:ℕ∞)) g) (j : Fin 2) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fourierMatchingResidual s k f g j) := by
  have hr := symmetricSource_parametric_smoothOn (V:=univ) isOpen_univ
    (H:=fun _ : ℝ×Coord3 => flatBackgroundTensor s) contDiffOn_const
    (fourierMatchingPair_smooth s k hf hg).contDiffOn j
  rw [contDiffOn_univ] at hr
  exact ((fourierResidualCutoff_smooth.comp
    ((contDiff_apply ℝ ℝ (0:Fin 3)).comp contDiff_snd)).neg).mul hr

lemma fourierMatchingResidual_periodic (s : Fin 3 → ℝ) (k : ℤ) {f g : ℝ×Coord3 → ℝ}
    (hf : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hg : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) (p : ℝ) (j : Fin 2) :
    AngularPeriodic (2*Real.pi) (fun x => fourierMatchingResidual s k f g j (p,x)) := by
  intro n x
  have he := symmetricSource_angular_translate (fourierMatchingPair_periodic s k hf hg p)
    (fun _ => flatBackgroundTensor s) j n x
  dsimp only [fourierMatchingResidual]
  rw [←he]
  simp only [Pi.add_apply,angularShift,Matrix.cons_val_zero,add_zero]

lemma fourierMatchingResidual_support (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (p : ℝ) (j : Fin 2) :
    tsupport (fun x => fourierMatchingResidual s k f g j (p,x))⊆{x | x 0∈Icc 1 5} := by
  apply closure_minimal _ (isClosed_Icc.preimage (continuous_apply 0))
  intro x hx
  constructor
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_left (le_of_not_ge hh),neg_zero,zero_mul])
  · by_contra hh
    exact hx (by simp only [fourierMatchingResidual,fourierResidualCutoff_zero_right (le_of_not_ge hh),neg_zero,zero_mul])

lemma flatPurePair_source_zero {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (k : ℤ) (j : Fin 2) (x : Coord3) :
    symmetricSource (fun _ => flatBackgroundTensor s) (fun y => ![y 0,flatPhaseMode s ![0,k] 0 y]) j x=0 := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => ![y 0,flatPhaseMode s ![0,k] 0 y]) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact contDiff_apply ℝ ℝ 0
    · exact flatPhaseMode_smooth s ![0,k] 0
  rw [flatBackgroundTensor_source hu]
  fin_cases j
  · change flatTensorLaplacian s (fun y : Coord3 => y 0) x=0
    simpa only [one_mul,add_zero] using flatTensorLaplacian_axial_affine s 1 0 x
  · exact flatPhaseMode_harmonic hs ![0,k] 0 x

lemma fourierMatchingResidual_base {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} (hf : ∀ x,f (0,x)=0) (hg : ∀ x,g (0,x)=0)
    (j : Fin 2) (x : Coord3) : fourierMatchingResidual s k f g j (0,x)=0 := by
  have he : (fun y => fourierMatchingPair s k f g (0,y))=
      (fun y => ![y 0,flatPhaseMode s ![0,k] 0 y]) := by
    funext y
    simp only [fourierMatchingPair,hf,hg,mul_zero,add_zero]
  unfold fourierMatchingResidual
  rw [he,flatPurePair_source_zero hs,mul_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_FourierMatchingFamilyCorrection
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.zeroVoltageJets_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma axial_torusRate_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) : 0<torusRate s ![0,k] := by
  have hb := torusRate_lower hs ![0,k]
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp := abs_pos.mpr hk'
  simp only [torusSize,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_zero,abs_zero,zero_add] at hb
  linarith

lemma fourierMatchingFamily_correction_oai {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {f g : ℝ×Coord3 → ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
    (hfz : ∀ x,f (0,x)=0) (hgz : ∀ x,g (0,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ p in 𝓝 (0:ℝ),periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
      (fun j y => fourierMatchingResidual s k f g j (p,y))=0 →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
        tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
        (∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) ∧
        ∀ x,‖H x‖≤ε := by
  have hF := fourierMatchingPair_smooth s k hfs hgs
  have hF0 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => fourierMatchingPair s k f g z 0) :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).comp hF
  have hF1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => fourierMatchingPair s k f g z 1) :=
    (contDiff_apply ℝ ℝ (1:Fin 2)).comp hF
  have hup (p : ℝ) : AngularPeriodic (2*Real.pi)
      (fun y => ![fourierMatchingPair s k f g (p,y) 0,fourierMatchingPair s k f g (p,y) 1]) :=
    fourierMatchingPair_periodic s k hfp hgp p
  have hub (x : Coord3) : fourierMatchingPair s k f g (0,x) 0=x 0 := by
    simp [fourierMatchingPair,hfz]
  have hvb (x : Coord3) : fourierMatchingPair s k f g (0,x) 1=
      pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x) := by
    simp [fourierMatchingPair,hgz,pureWallMode_eq_flatPhaseMode]
  have hlam := axial_torusRate_pos hs hk
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  exact periodic_pure_mode_family_correction hF0 hF1 (0:ℝ)
    (by norm_num : (1:ℝ)≠0) hlam.ne' hk' (by positivity : 0<2*Real.pi)
    (by norm_num : (1/2:ℝ)<1) (by norm_num : (5:ℝ)<11/2) hub hvb hup
    (fourierMatchingResidual_smooth s k hfs hgs)
    (fourierMatchingResidual_base hs k hfz hgz)
    (fun j p => fourierMatchingResidual_periodic s k hfp hgp p j)
    (fun j p => fourierMatchingResidual_support s k f g p j) hε

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.fourierMatchingFamily_correction_oai := @OAI.ScalarConductivity.fourierMatchingFamily_correction_oai
