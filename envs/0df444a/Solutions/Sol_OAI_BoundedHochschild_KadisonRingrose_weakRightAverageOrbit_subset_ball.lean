-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.weakRightAverageOrbit_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:51:20.495857+00:00
-- url     : https://prove2.me/submissions/3749423f-ae69-40dc-bd7a-39cbf197cf23

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_countable_isometries

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem predual_tendsto_mul_left (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => a*b i) l (a*c) :=
  HasPreadjoint.tendsto e (mul_hasPreadjoint e a) hb

theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (S : Set M) (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) (hproj : ∀ q ∈ S, IsStarProjection q) :
    ∃ p : M, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) ∧
      ∃ U : Ultrafilter S, (U : Filter S) ≤ atTop ∧
        PredualTendsto e (fun q : S => (q : M)) (U : Filter S) p := by
  classical
  let : Nonempty S := hne.to_subtype
  let : IsDirectedOrder S := ⟨fun a b => by
    rcases hchain.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter S := Ultrafilter.of atTop
  have hU : (U : Filter S) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨p, _, ht⟩ := exists_predual_ultralimit e U (fun q : S => (q : M)) 1
    (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  have hp : IsStarProjection p := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e p ht
      have heq : (fun q : S => (q : M) * p) = (fun q : S => (q : M)) :=
        funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hs := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun q : S => star (q : M)) = (fun q : S => (q : M)) := by
        funext q
        exact (hproj q q.property).isSelfAdjoint.star_eq
      rw [heq] at hs
      exact predual_tendsto_unique e hs ht
  refine ⟨p, hp, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hu
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hu q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) :=
      funext fun q => ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso

lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul

lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma norm_le_one (v : PartialIso M) : ‖(v : M)‖ ≤ 1 := by
  have hi := v.initial_proj.norm_le _
  have he : ‖(v : M)‖ * ‖(v : M)‖ = ‖v.initial‖ := by
    exact CStarRing.norm_star_mul_self.symm
  nlinarith [norm_nonneg (v : M)]

variable [PartialOrder M]

variable [StarOrderedRing M]

omit [StarOrderedRing M] in
lemma initial_mono {v w : PartialIso M} (h : v ≤ w) : v.initial ≤ w.initial := h.1

lemma star_mul_of_le {v w : PartialIso M} (h : v ≤ w) : star (v : M) * w = v.initial := by
  have hv := congrArg star h.2
  simp only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] at hv
  calc
    star (v : M) * w = (v.initial * star (w : M)) * w := by rw [hv]
    _ = v.initial * w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1
lemma star_mul_of_ge {v w : PartialIso M} (h : v ≤ w) : star (w : M) * v = v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)
lemma final_mono {v w : PartialIso M} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  calc
    w.final * v.final = (w : M) * (star (w : M) * v) * star (v : M) := by
      simp only [final,mul_assoc]
    _ = (w : M) * v.initial * star (v : M) := by rw [star_mul_of_ge h]
    _ = v.final := by rw [h.2]; rfl

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma mul_star_eq_zero_of_initial_orthogonal {v w : PartialIso M}
    (h : v.initial*w.initial=0) : (v : M)*star (w : M)=0 := by
  have hw : w.initial*star (w : M)=star (w : M) := by
    simpa only [star_mul,star_star,w.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star w.mul_initial
  calc
    (v : M)*star (w : M) = ((v : M)*v.initial)*(w.initial*star (w : M)) := by
      rw [v.mul_initial,hw]
    _ = (v : M)*(v.initial*w.initial)*star (w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma orthogonal_initial_symm {v w : PartialIso M} (h : v.initial*w.initial=0) :
    w.initial*v.initial=0 := by
  simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
    w.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h
lemma orthogonal_final_symm {v w : PartialIso M} (h : v.final*w.final=0) :
    w.final*v.final=0 := by
  simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : PartialIso M where
  val := (v : M)+w
  mul_star_mul := by
    have hab := mul_star_eq_zero_of_initial_orthogonal hi
    have hba := mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi)
    have hab' := star_mul_eq_zero_of_final_orthogonal hf
    have hba' := star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf)
    simp only [star_add,mul_add,add_mul,hab,hba,zero_add,add_zero]
    rw [v.mul_star_mul,w.mul_star_mul,mul_assoc,mul_assoc,hab',hba',mul_zero,mul_zero]
    abel

lemma orthogonalSum_initial (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).initial=v.initial+w.initial := by
  change star ((v : M)+w)*((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,star_mul_eq_zero_of_final_orthogonal hf,
    star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf),zero_add,add_zero,initial]
lemma orthogonalSum_final (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).final=v.final+w.final := by
  change ((v : M)+w)*star ((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,mul_star_eq_zero_of_initial_orthogonal hi,
    mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi),zero_add,add_zero,final]
end
end PartialIso
end HochschildComparison
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_partialIso_chain_supremum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : PartialIso M, (∀ v ∈ c, v ≤ w) ∧
      (∀ z : PartialIso M, (∀ v ∈ c, v ≤ z) → w ≤ z) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.initial ≤ r) → w.initial ≤ r) ∧
      (∀ r : M, IsStarProjection r → (∀ v ∈ c, v.final ≤ r) → w.final ≤ r) := by
  classical
  let S : Set M := PartialIso.initial '' c
  have hSne : S.Nonempty := hne.image _
  have hSchain : IsChain (· ≤ ·) S := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _
    exact (hc.total hv hw).imp PartialIso.initial_mono PartialIso.initial_mono
  have hSproj : ∀ r ∈ S, IsStarProjection r := by
    rintro _ ⟨v, _, rfl⟩
    exact v.initial_proj
  obtain ⟨p, hp, hupper, hleast, hann, _⟩ :=
    exists_projection_chain_supremum_with_limit e S hSne hSchain hSproj
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := ⟨fun a b => by
    rcases hc.total a.property b.property with hab | hba
    · exact ⟨b, hab, le_rfl⟩
    · exact ⟨a, le_rfl, hba⟩⟩
  let U : Ultrafilter c := Ultrafilter.of atTop
  have hU : (U : Filter c) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨V, _, ht⟩ := exists_predual_ultralimit e U
    (fun v : c => ((v : PartialIso M) : M)) 1 (fun v => v.val.norm_le_one)
  have hVi (v : c) : V * v.val.initial = (v.val : M) := by
    have hm := HochschildSakai.predual_tendsto_mul_right e v.val.initial ht
    have heq : (fun w : c => (w.val : M) * v.val.initial) =ᶠ[U]
        (fun _ => (v.val : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact hvw.2
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hstarVi (v : c) : star V * (v.val : M) = v.val.initial := by
    have hm := HochschildSakai.predual_tendsto_mul_right e (v.val : M)
      (HochschildSakai.predual_tendsto_star e ht)
    have heq : (fun w : c => star (w.val : M) * (v.val : M)) =ᶠ[U]
        (fun _ => v.val.initial) := by
      apply hU
      filter_upwards [eventually_ge_atTop v] with w hvw
      exact PartialIso.star_mul_of_ge hvw
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr'
      (heq.mono fun _ h => congrArg (fun a : M => e.symm a x) h.symm)
  have hVp : V * p = V := by
    have hm := HochschildSakai.predual_tendsto_mul_right e p ht
    have heq : (fun v : c => (v.val : M) * p) =
        (fun v : c => (v.val : M)) := by
      funext v
      calc
        (v.val : M) * p = ((v.val : M) * v.val.initial) * p := by
          rw [v.val.mul_initial]
        _ = (v.val : M) := by
          rw [mul_assoc, (v.val.initial_proj.le_iff_mul_eq_left hp).mp
            (hupper _ ⟨v.val, v.property, rfl⟩), v.val.mul_initial]
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  have hpstar : p * star V = star V := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hVp
  have hVV : star V * V = p := by
    have hann' : p * (star V * V - p) = 0 := by
      apply hann
      rintro _ ⟨v, hv, rfl⟩
      have hfixed : v.initial * (star V * V) = v.initial := by
        have hs : v.initial * star V = star (v : M) := by
          simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] using
            congrArg star (hVi ⟨v, hv⟩)
        calc
          v.initial * (star V * V) = star (v : M) * V := by rw [← mul_assoc, hs]
          _ = v.initial := by
            simpa only [star_mul, star_star, v.initial_proj.isSelfAdjoint.star_eq]
              using congrArg star (hstarVi ⟨v, hv⟩)
      rw [mul_sub, hfixed, (v.initial_proj.le_iff_mul_eq_left hp).mp
        (hupper _ ⟨v, hv, rfl⟩), sub_self]
    rw [mul_sub, ← mul_assoc, hpstar, hp.isIdempotentElem.eq] at hann'
    exact sub_eq_zero.mp hann'
  let w : PartialIso M := ⟨V, by rw [mul_assoc, hVV, hVp]⟩
  have hwi : w.initial = p := hVV
  have hwupper : ∀ v ∈ c, v ≤ w := by
    intro v hv
    exact ⟨by rw [hwi]; exact hupper _ ⟨v, hv, rfl⟩, hVi ⟨v, hv⟩⟩
  refine ⟨w, hwupper, ?_, ?_, ?_⟩
  · intro z hz
    have hpz : p ≤ z.initial := by
      apply hleast z.initial z.initial_proj
      rintro _ ⟨v, hv, rfl⟩
      exact (hz v hv).1
    have hzp : (z : M) * p = V := by
      have ha : p * star ((z : M) - V) = 0 := by
        apply hann
        rintro _ ⟨v, hv, rfl⟩
        have heq : ((z : M) - V) * v.initial = 0 := by
          rw [sub_mul, (hz v hv).2, hVi ⟨v, hv⟩, sub_self]
        simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq, star_zero]
          using congrArg star heq
      have ha' : ((z : M) - V) * p = 0 := by
        simpa only [star_mul, star_star, hp.isSelfAdjoint.star_eq, star_zero]
          using congrArg star ha
      rwa [sub_mul, hVp, sub_eq_zero] at ha'
    exact ⟨by rw [hwi]; exact hpz, by change (z : M) * w.initial = V; rw [hwi, hzp]⟩
  · intro r hr hb
    rw [hwi]
    apply hleast r hr
    rintro _ ⟨v, hv, rfl⟩
    exact hb v hv
  · intro r hr hb
    have hrV : r * V = V := by
      have hm := HochschildSakai.predual_tendsto_mul_left e r ht
      have heq : (fun v : c => r * (v.val : M)) =
          (fun v : c => (v.val : M)) := by
        funext v
        calc
          r * (v.val : M) = r * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = (v.val : M) := by
            rw [← mul_assoc, (v.val.final_proj.le_iff_mul_eq_right hr).mp
              (hb v.val v.property), v.val.final_mul]
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    apply (w.final_proj.le_iff_mul_eq_right hr).mpr
    change r * (V * star V) = V * star V
    rw [← mul_assoc, hrV]
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildRigidity HochschildDiffuse HochschildComparison
open FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_orthogonal_of_le_complement {s c : M}
    (hs : IsStarProjection s) (hc : IsStarProjection c) (hcs : c ≤ 1-s) : s*c=0 := by
  have h := (hc.le_iff_mul_eq_right hs.one_sub).mp hcs
  rw [sub_mul,one_mul] at h
  exact sub_eq_self.mp h
end HochschildTypeII
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))

lemma orthogonal_projection_sum_annihilator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (a P : M)
    (ht : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P)
    (hpa : ∀ i, p i * a = 0) : P * a = 0 := by
  classical
  have hm := HochschildSakai.predual_tendsto_mul_right e a ht
  have heq : (fun s : Finset I => (∑ i ∈ s, p i) * a) = fun _ => (0 : M) := by
    funext s
    rw [Finset.sum_mul]
    simp only [hpa, Finset.sum_const_zero]
  rw [heq] at hm
  exact predual_tendsto_unique e hm (predual_tendsto_const e 0 atTop)
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {I : Type*}

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIso_finset_sum_data (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) :
    ∃ w : PartialIso M, (w : M) = ∑ i ∈ s, (v i : M) ∧
      w.initial = ∑ i ∈ s, (v i).initial ∧ w.final = ∑ i ∈ s, (v i).final := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert i s his ih =>
      obtain ⟨w, hw, hwi, hwf⟩ := ih
      have hI : (v i).initial * w.initial = 0 := by
        rw [hwi, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hi i j (fun h => his (h ▸ hj)))
      have hF : (v i).final * w.final = 0 := by
        rw [hwf, Finset.mul_sum]
        exact Finset.sum_eq_zero (fun j hj => hf i j (fun h => his (h ▸ hj)))
      refine ⟨(v i).orthogonalSum w hI hF, ?_, ?_, ?_⟩
      · change (v i : M) + (w : M) = _
        rw [hw, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_initial, hwi, Finset.sum_insert his]
      · rw [PartialIso.orthogonalSum_final, hwf, Finset.sum_insert his]

def partialIsoFinsetSum (v : I → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (s : Finset I) : PartialIso M :=
  (partialIso_finset_sum_data v hi hf s).choose

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_coe (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s : M) = ∑ i ∈ s, (v i : M) :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_initial (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).initial = ∑ i ∈ s, (v i).initial :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma partialIsoFinsetSum_final (v : I → PartialIso M) (hi hf) (s : Finset I) :
    (partialIsoFinsetSum v hi hf s).final = ∑ i ∈ s, (v i).final :=
  (partialIso_finset_sum_data v hi hf s).choose_spec.2.2

lemma partialIsoFinsetSum_mono (v : I → PartialIso M) (hi hf)
    {s t : Finset I} (hst : s ⊆ t) :
    partialIsoFinsetSum v hi hf s ≤ partialIsoFinsetSum v hi hf t := by
  classical
  constructor
  · rw [partialIsoFinsetSum_initial, partialIsoFinsetSum_initial]
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (v i).initial_proj.nonneg)
  · rw [partialIsoFinsetSum_coe, partialIsoFinsetSum_initial, Finset.mul_sum,
      partialIsoFinsetSum_coe]
    apply Finset.sum_congr rfl
    intro i his
    rw [Finset.sum_mul]
    calc
      _ = (v i : M) * (v i).initial := Finset.sum_eq_single i (fun j _ hji => ?_)
        (fun hit => (hit (hst his)).elim)
      _ = (v i : M) := (v i).mul_initial
    calc
        (v j : M) * (v i).initial = ((v j : M) * (v j).initial) * (v i).initial := by
          rw [(v j).mul_initial]
        _ = 0 := by rw [mul_assoc, hi j i hji, mul_zero]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_countable_partialIso_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (v : ℕ → PartialIso M)
    (hi : ∀ i j, i ≠ j → (v i).initial * (v j).initial = 0)
    (hf : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    ∃ w : PartialIso M, (∀ i, (v i).initial ≤ w.initial) ∧
      (∀ i, (v i).final ≤ w.final) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).initial ≤ p) → w.initial ≤ p) ∧
      (∀ p : M, IsStarProjection p → (∀ i, (v i).final ≤ p) → w.final ≤ p) := by
  classical
  let V (n : ℕ) := partialIsoFinsetSum v hi hf (Finset.range n)
  have hm : Monotone V := fun _ _ h => partialIsoFinsetSum_mono v hi hf (Finset.range_mono h)
  have hc : IsChain (· ≤ ·) (Set.range V) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact (le_total i j).imp (fun h => hm h) (fun h => hm h)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e (Set.range V) hc
    ⟨V 0, Set.mem_range_self 0⟩
  have hsumI (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).initial ≤ p) (n : ℕ) :
      (V n).initial ≤ p := by
    apply ((V n).initial_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_initial, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).initial_proj.le_iff_mul_eq_right hp).mp (h i))
  have hsumF (p : M) (hp : IsStarProjection p) (h : ∀ i, (v i).final ≤ p) (n : ℕ) :
      (V n).final ≤ p := by
    apply ((V n).final_proj.le_iff_mul_eq_right hp).mpr
    rw [partialIsoFinsetSum_final, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => ((v i).final_proj.le_iff_mul_eq_right hp).mp (h i))
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro i
    apply le_trans _ (hw (V (i + 1)) (Set.mem_range_self _)).1
    rw [partialIsoFinsetSum_initial]
    exact Finset.single_le_sum (fun j _ => (v j).initial_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro i
    apply le_trans _ (PartialIso.final_mono (hw (V (i + 1)) (Set.mem_range_self _)))
    rw [partialIsoFinsetSum_final]
    exact Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg)
      (Finset.mem_range.mpr (Nat.lt_succ_self i))
  · intro p hp h
    apply hwi p hp
    rintro _ ⟨n, rfl⟩
    exact hsumI p hp h n
  · intro p hp h
    apply hwf p hp
    rintro _ ⟨n, rfl⟩
    exact hsumF p hp h n
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_transition_initial (v w : PartialIso M) (h : v.initial = w.initial) :
    star ((v : M) * star (w : M)) * ((v : M) * star (w : M)) = w.final := by
  calc
    _ = (w : M) * v.initial * star (w : M) := by
      simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
    _ = w.final := by rw [h, w.mul_initial]; rfl

def columnTransition (v w : PartialIso M) (h : v.initial = w.initial) : PartialIso M :=
  ⟨(v : M) * star (w : M), by
    rw [mul_assoc, column_transition_initial v w h]
    have hw : star (w : M) * w.final = star (w : M) := by
      simpa only [star_mul, star_star, w.final_proj.isSelfAdjoint.star_eq] using
        congrArg star w.final_mul
    rw [mul_assoc, hw]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_initial (v w : PartialIso M) (h) :
    (columnTransition v w h).initial = w.final := column_transition_initial v w h

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_final (v w : PartialIso M) (h) :
    (columnTransition v w h).final = v.final := by
  change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = _
  rw [star_mul, star_star]
  calc
    _ = (v : M) * w.initial * star (v : M) := by simp only [PartialIso.initial, mul_assoc]
    _ = v.final := by rw [← h, v.mul_initial]; rfl

lemma projection_le_complement_of_mul_zero {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) : p ≤ 1 - q := by
  apply (hp.le_iff_mul_eq_left hq.one_sub).mpr
  rw [mul_sub, mul_one, hpq, sub_zero]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_eq_one_of_column_bounds (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    {p : M} (hp : IsStarProjection p) (h : ∀ i, (c i).final ≤ p) : p = 1 := by
  have hh := orthogonal_projection_sum_annihilator e (fun i => (c i).final) (1 - p) 1 ht
    (fun i => by
      rw [mul_sub, mul_one, ((c i).final_proj.le_iff_mul_eq_left hp).mp (h i), sub_self])
  rw [one_mul, sub_eq_zero] at hh
  exact hh.symm

theorem finite_columns_of_countable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧ ∑ j, (v j).final = 1 := by
  classical
  let σ := (Nat.divModEquiv n).symm
  let a (j : Fin n) (i : ℕ) := columnTransition (c (σ (i, j))) (c i)
    ((hi _).trans (hi _).symm)
  have hai (j i) : (a j i).initial = (c i).final := columnTransition_initial ..
  have haf (j i) : (a j i).final = (c (σ (i, j))).final := columnTransition_final ..
  have haI (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).initial * (a j k).initial = 0 := by
    rw [hai, hai]
    exact ho i k hik
  have haF (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).final * (a j k).final = 0 := by
    rw [haf, haf]
    exact ho _ _ (fun h => hik (congrArg Prod.fst (σ.injective h)))
  choose v hvi hvf hvi_min hvf_min using fun j => exists_countable_partialIso_sum e
    (a j) (haI j) (haF j)
  have hinit (j : Fin n) : (v j).initial = 1 := by
    apply projection_eq_one_of_column_bounds e c ht (v j).initial_proj
    intro i
    rw [← hai j i]
    exact hvi j i
  have hcross (j k : Fin n) (hjk : j ≠ k) (i l : ℕ) :
      (a j i).final * (a k l).final = 0 := by
    rw [haf, haf]
    exact ho _ _ (fun h => hjk (congrArg Prod.snd (σ.injective h)))
  have horth (j k : Fin n) (hjk : j ≠ k) : (v j).final * (v k).final = 0 := by
    have hfirst (i : ℕ) : (a j i).final * (v k).final = 0 := by
      have hb : (v k).final ≤ 1 - (a j i).final := by
        apply hvf_min k _ (a j i).final_proj.one_sub
        intro l
        apply projection_le_complement_of_mul_zero (a k l).final_proj (a j i).final_proj
        simpa only [star_mul, (a j i).final_proj.isSelfAdjoint.star_eq,
          (a k l).final_proj.isSelfAdjoint.star_eq, star_zero] using
          congrArg star (hcross j k hjk i l)
      exact HochschildTypeII.projection_orthogonal_of_le_complement (a j i).final_proj
        (v k).final_proj hb
    have hb : (v j).final ≤ 1 - (v k).final := hvf_min j _ (v k).final_proj.one_sub
      (fun i => projection_le_complement_of_mul_zero (a j i).final_proj (v k).final_proj (hfirst i))
    have h := ((v j).final_proj.le_iff_mul_eq_left (v k).final_proj.one_sub).mp hb
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  have hp : IsStarProjection (∑ j, (v j).final) :=
    orthogonal_projection_finset_sum (fun j => (v j).final) (fun j => (v j).final_proj)
      horth Finset.univ
  have hsum : (∑ j, (v j).final) = 1 := by
    apply projection_eq_one_of_column_bounds e c ht hp
    intro i
    let t := Nat.divModEquiv n i
    have hti : σ t = i := (Nat.divModEquiv n).symm_apply_apply i
    have hh : (c i).final ≤ (v t.2).final := by
      have h := hvf t.2 t.1
      rw [haf] at h
      change (c (σ t)).final ≤ _ at h
      simpa only [hti] using h
    exact hh.trans (Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg) (Finset.mem_univ t.2))
  exact ⟨v, hinit, horth, hsum⟩

theorem exists_properlyInfinite_matrix_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧ ∑ j, (v j).final = 1 := by
  obtain ⟨c, hi, ho, ht⟩ := exists_countable_isometries e hno
  exact finite_columns_of_countable e c hi ho ht n
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
  (hs : ∑ i, (c i).final = 1)

include hi ho in
lemma column_star_mul (i j : Fin n) :
    star (c i : M) * (c j : M) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst j
    exact hi i
  · exact PartialIso.star_mul_eq_zero_of_final_orthogonal (ho i j h)

def columnCompression (a : M) : CStarMatrix (Fin n) (Fin n) M :=
  CStarMatrix.ofMatrix (fun i j => star (c i : M) * a * (c j : M))

def columnReconstruction (A : CStarMatrix (Fin n) (Fin n) M) : M :=
  ∑ i, ∑ j, (c i : M) * A i j * star (c j : M)

include hs in
lemma columnReconstruction_compression (a : M) :
    columnReconstruction c (columnCompression c a) = a := by
  calc
    _ = ∑ i, ((c i : M) * star (c i : M)) * a * (∑ j, (c j : M) * star (c j : M)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (c i : M) * (star (c i : M) * a * (c j : M)) * star (c j : M) = _
      simp only [mul_assoc]
    _ = a := by
      change (∑ i, (c i).final * a * (∑ j, (c j).final)) = a
      rw [hs]
      simp only [mul_one]
      rw [← Finset.sum_mul, hs, one_mul]

include hi ho in
lemma columnCompression_reconstruction (A : CStarMatrix (Fin n) (Fin n) M) :
    columnCompression c (columnReconstruction c A) = A := by
  classical
  ext i j
  change star (c i : M) * (∑ k, ∑ l, (c k : M) * A k l * star (c l : M)) * (c j : M) = A i j
  calc
    _ = ∑ k, ∑ l, (star (c i : M) * (c k : M)) * A k l *
        (star (c l : M) * (c j : M)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      simp only [mul_assoc]
    _ = A i j := by simp [column_star_mul c hi ho]

include hs in
lemma columnCompression_mul (a b : M) :
    columnCompression c (a * b) = columnCompression c a * columnCompression c b := by
  ext i j
  change star (c i : M) * (a * b) * (c j : M) =
    ∑ k, (star (c i : M) * a * (c k : M)) * (star (c k : M) * b * (c j : M))
  calc
    _ = star (c i : M) * a * (∑ k, (c k : M) * star (c k : M)) * b * (c j : M) := by
      change _ = star (c i : M) * a * (∑ k, (c k).final) * b * (c j : M)
      rw [hs, mul_one]
      simp only [mul_assoc]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_assoc]

def columnMatrixEquiv : M ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) M where
  toFun := columnCompression c
  invFun := columnReconstruction c
  left_inv := columnReconstruction_compression c hs
  right_inv := columnCompression_reconstruction c hi ho
  map_mul' := columnCompression_mul c hs
  map_add' a b := by
    ext i j
    change star (c i : M) * (a + b) * (c j : M) =
      star (c i : M) * a * (c j : M) + star (c i : M) * b * (c j : M)
    rw [mul_add, add_mul]
  map_smul' z a := by
    ext i j
    change star (c i : M) * (z • a) * (c j : M) = z • (star (c i : M) * a * (c j : M))
    rw [mul_smul_comm, smul_mul_assoc]
  map_star' a := by
    ext i j
    change star (c i : M) * star a * (c j : M) = star (star (c j : M) * a * (c i : M))
    simp only [star_mul, star_star, mul_assoc]

variable [PartialOrder M] [StarOrderedRing M]

include hi ho hs in
lemma columnCompression_norm (a : M) : ‖columnCompression c a‖ = ‖a‖ := by
  change ‖columnMatrixEquiv c hi ho hs a‖ = ‖a‖
  exact StarAlgEquiv.norm_map (columnMatrixEquiv c hi ho hs) a
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] {n : ℕ}
variable (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

def columnRow (x : Fin n → M) : M := ∑ i, x i * star (c i : M)

def columnColumn (y : Fin n → M) : M := ∑ i, (c i : M) * y i

include hi ho in
lemma columnRow_mul_column (x y : Fin n → M) :
    columnRow c x * columnColumn c y = ∑ i, x i * y i := by
  classical
  calc
    _ = ∑ i, ∑ j, x i * (star (c i : M) * (c j : M)) * y j := by
      simp only [columnRow, columnColumn]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc]
    _ = _ := by simp [column_star_mul c hi ho]

include hi ho in
lemma columnRow_mul_star (x : Fin n → M) :
    columnRow c x * star (columnRow c x) = ∑ i, x i * star (x i) := by
  have hs : star (columnRow c x) = columnColumn c (fun i => star (x i)) := by
    simp only [columnRow, columnColumn, star_sum, star_mul, star_star]
  rw [hs, columnRow_mul_column c hi ho]

include hi ho in
lemma star_column_mul_column (y : Fin n → M) :
    star (columnColumn c y) * columnColumn c y = ∑ i, star (y i) * y i := by
  have hs : star (columnColumn c y) = columnRow c (fun i => star (y i)) := by
    simp only [columnRow, columnColumn, star_sum, star_mul]
  rw [hs, columnRow_mul_column c hi ho]

include hi ho in
lemma columnRow_norm_sq (x : Fin n → M) :
    ‖columnRow c x‖ ^ 2 = ‖∑ i, x i * star (x i)‖ := by
  rw [sq, ← CStarRing.norm_self_mul_star, columnRow_mul_star c hi ho]

include hi ho in
lemma columnColumn_norm_sq (y : Fin n → M) :
    ‖columnColumn c y‖ ^ 2 = ‖∑ i, star (y i) * y i‖ := by
  rw [sq, ← CStarRing.norm_star_mul_self, star_column_mul_column c hi ho]

include hi ho in

lemma finite_row_column_estimate (x y : Fin n → M) :
    ‖∑ i, x i * y i‖ ^ 2 ≤ ‖∑ i, x i * star (x i)‖ * ‖∑ i, star (y i) * y i‖ := by
  rw [← columnRow_mul_column c hi ho]
  calc
    _ ≤ (‖columnRow c x‖ * ‖columnColumn c y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) 2
    _ = _ := by rw [mul_pow, columnRow_norm_sq c hi ho, columnColumn_norm_sq c hi ho]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

def HasFiniteRowBound (T : M →L[ℂ] M) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → M),
    ‖∑ i, T (x i) * star (T (x i))‖ ≤ C ^ 2 * ‖∑ i, x i * star (x i)‖

variable {I : Type*} [Fintype I]

variable {n : ℕ}

theorem finiteRightAverage_norm_of_rowBound
    (c : Fin n → HochschildComparison.PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (m : Fin n → M) (hm : ∑ i, m i * star (m i) = 1)
    (T : M →L[ℂ] M) {C : ℝ} (hT : HasFiniteRowBound T C) :
    ‖finiteRightAverage m T‖ ≤ C := by
  by_cases hM : Nontrivial M
  · let := hM
    apply ContinuousLinearMap.opNorm_le_bound _ hT.1
    intro a
    have hin : (∑ i, (a * m i) * star (a * m i)) = a * star a := by
      calc
        _ = a * (∑ i, m i * star (m i)) * star a := by
          simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
        _ = a * star a := by rw [hm, mul_one]
    have hs : ‖finiteRightAverage m T a‖ ^ 2 ≤ C ^ 2 * ‖a‖ ^ 2 := by
      rw [finiteRightAverage_apply]
      calc
        _ ≤ ‖∑ i, T (a * m i) * star (T (a * m i))‖ *
            ‖∑ i, star (star (m i)) * star (m i)‖ :=
          finite_row_column_estimate c hi ho (fun i => T (a * m i)) (fun i => star (m i))
        _ = ‖∑ i, T (a * m i) * star (T (a * m i))‖ := by
          simp only [star_star, hm, norm_one, mul_one]
        _ ≤ C ^ 2 * ‖∑ i, (a * m i) * star (a * m i)‖ := hT.2 n (fun i => a * m i)
        _ = C ^ 2 * ‖a‖ ^ 2 := by simp only [hin, CStarRing.norm_self_mul_star, sq]
    have hnonneg : 0 ≤ C * ‖a‖ := mul_nonneg hT.1 (norm_nonneg a)
    nlinarith [norm_nonneg (finiteRightAverage m T a)]
  · let : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    have hz : finiteRightAverage m T = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    exact hT.1
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma left_isometry_norm {v : M} (hv : star v * v = 1) (a : M) : ‖v * a‖ = ‖a‖ := by
  have h : star (v * a) * (v * a) = star a * a := by
    rw [star_mul]
    calc
      _ = star a * (star v * v) * a := by simp only [mul_assoc]
      _ = star a * a := by rw [hv, mul_one]
  have hn : ‖v * a‖ ^ 2 = ‖a‖ ^ 2 := by
    simpa only [CStarRing.norm_star_mul_self, ← sq] using congrArg norm h
  nlinarith [norm_nonneg (v * a), norm_nonneg a]

variable {n : ℕ} (c : Fin n → PartialIso M)
  (hi : ∀ i, (c i).initial = 1)
  (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma columnRow_mul_isometry (x : Fin n → M) (j : Fin n) :
    columnRow c x * (c j : M) = x j := by
  classical
  calc
    _ = ∑ i, x i * (star (c i : M) * (c j : M)) := by
      simp only [columnRow, Finset.sum_mul, mul_assoc]
    _ = x j := by simp [column_star_mul c hi ho]

omit [PartialOrder M] [StarOrderedRing M] in
include hi ho in
lemma columnCompression_row (x : Fin n → M) (k i j : Fin n) :
    columnCompression c ((c k : M) * columnRow c x) i j = if i = k then x j else 0 := by
  change star (c i : M) * ((c k : M) * columnRow c x) * (c j : M) = _
  calc
    _ = (star (c i : M) * (c k : M)) * (columnRow c x * (c j : M)) := by
      simp only [mul_assoc]
    _ = _ := by rw [column_star_mul c hi ho, columnRow_mul_isometry c hi ho]; split_ifs <;> simp

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finiteRowBound_of_completelyBounded (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : HasFiniteRowBound T C := by
  refine ⟨hT.1, ?_⟩
  intro n x
  cases n with
  | zero => simp
  | succ n =>
      obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
      let k : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
      have hmap : (columnCompression c ((c k : M) * columnRow c x)).map T =
          columnCompression c ((c k : M) * columnRow c (fun i => T (x i))) := by
        ext i j
        rw [CStarMatrix.map_apply, columnCompression_row c hi ho, columnCompression_row c hi ho]
        split_ifs <;> simp
      have hb := hT.2 (n + 1) (columnCompression c ((c k : M) * columnRow c x))
      rw [hmap, columnCompression_norm c hi ho hs, columnCompression_norm c hi ho hs,
        left_isometry_norm (hi k), left_isometry_norm (hi k)] at hb
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow, columnRow_norm_sq c hi ho, columnRow_norm_sq c hi ho] at hb2
      exact hb2

theorem finiteRightAverage_norm_of_completelyBounded
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (m : Fin (n + 1) → M) (hm : ∑ i, m i * star (m i) = 1)
    (T : M →L[ℂ] M) {C : ℝ} (hT : CompletelyBoundedEstimate T C) :
    ‖finiteRightAverage m T‖ ≤ C := by
  obtain ⟨c, hi, ho, _⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
  exact finiteRightAverage_norm_of_rowBound c hi ho m hm T
    (finiteRowBound_of_completelyBounded e hno T hT)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma weakOperatorImage_mem (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) {C : ℝ} (hT : ‖T‖ ≤ C) :
    weakOperatorImage e T ∈ weakOperatorBall C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply DFunLike.ext
    intro x
    simp only [weakOperatorImage, map_add]
  · intro z a
    apply DFunLike.ext
    intro x
    simp only [weakOperatorImage, map_smul,
      LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply]
  · intro a
    change ‖e.symm (T a)‖ ≤ C * ‖a‖
    rw [e.symm.norm_map]
    exact (T.le_opNorm a).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg a))

lemma weakOperatorBall_isClosed (C : ℝ) :
    IsClosed (weakOperatorBall (M := M) (X := X) C) := by
  have hadd : IsClosed {F : M → WeakDual ℂ X | ∀ a b, F (a + b) = F a + F b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  have hsmul : IsClosed {F : M → WeakDual ℂ X |
      ∀ (z : ℂ) a, F (z • a) = star z • F a} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun z => isClosed_iInter fun a =>
      isClosed_eq (continuous_apply (z • a)) ((continuous_apply a).const_smul (star z))
  have hbound : IsClosed {F : M → WeakDual ℂ X |
      ∀ a, ‖WeakDual.toStrongDual (F a)‖ ≤ C * ‖a‖} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    have h := (WeakDual.isClosed_closedBall (0 : StrongDual ℂ X) (C * ‖a‖)).preimage
      (continuous_apply a : Continuous (fun F : M → WeakDual ℂ X => F a))
    convert h using 1
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  exact hadd.inter (hsmul.inter hbound)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma rightAverageOrbit_norm_le (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) {S : N →L[ℂ] N}
    (hS : S ∈ rightAverageOrbit T) : ‖S‖ ≤ C := by
  obtain ⟨n, m, hm, rfl⟩ := hS
  cases n with
  | zero =>
      have heq : finiteRightAverage m T = 0 := by
        ext a
        simp only [finiteRightAverage_apply, Fin.sum_univ_zero, zero_apply]
      rw [heq, norm_zero]
      exact hT.1
  | succ n => exact finiteRightAverage_norm_of_completelyBounded e hno m hm T hT

lemma weakRightAverageOrbit_subset_ball (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : weakRightAverageOrbit e T ⊆ weakOperatorBall C := by
  apply closure_minimal _ (weakOperatorBall_isClosed C)
  rintro F ⟨S, hS, rfl⟩
  exact weakOperatorImage_mem e S (rightAverageOrbit_norm_le e hno T hT hS)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.weakRightAverageOrbit_subset_ball.{u} := @OAI.BoundedHochschild.KadisonRingrose.weakRightAverageOrbit_subset_ball.{u}
