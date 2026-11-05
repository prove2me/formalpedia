-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.exists_finite_right_module_average
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:05:04.875801+00:00
-- url     : https://prove2.me/submissions/3914d354-972f-404a-b5de-319ff77d2b9d

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_countable_isometries
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_weakRightAverageOrbit_subset_ball
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_central_support_row
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normalGNS_nontrivial
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_represented_factorization
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_minimal_represented_averages
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_compressed_norm_eq_on_minimal_family
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_projection_defect_eq_zero

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

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_projection_chain_supremum_with_limit
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
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
  obtain ⟨p, _hpnorm, ht⟩ := exists_predual_ultralimit e U
    (fun q : S => (q : M)) 1 (fun q => (hproj q q.property).norm_le)
  have hfixed (q : S) : (q : M) * p = q := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (q : M) ht
    have heq : (fun r : S => (q : M) * r) =ᶠ[U] (fun _ => (q : M)) := by
      apply hU
      filter_upwards [eventually_ge_atTop q] with r hqr
      exact ((hproj q q.property).le_iff_mul_eq_left (hproj r r.property)).mp hqr
    apply predual_tendsto_unique e hm
    intro z
    exact tendsto_const_nhds.congr' (heq.mono fun _ hr => congrArg (fun a : M => e.symm a z) hr.symm)
  have hpcentral (a : M) : p * a = a * p := by
    have hl := HochschildSakai.predual_tendsto_mul_left e a ht
    have hr := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => a * (q : M)) = (fun q : S => (q : M) * a) := by
      funext q
      exact (hcentral q q.property a).symm
    rw [heq] at hl
    exact predual_tendsto_unique e hr hl
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
  refine ⟨p, hp, hpcentral, ?_, ?_, ?_, U, hU, ht⟩
  · intro q hq
    exact ((hproj q hq).le_iff_mul_eq_left hp).mpr (hfixed ⟨q, hq⟩)
  · intro r hr hub
    apply (hp.le_iff_mul_eq_left hr).mpr
    have hm := HochschildSakai.predual_tendsto_mul_right e r ht
    have heq : (fun q : S => (q : M) * r) = (fun q : S => (q : M)) := by
      funext q
      exact ((hproj q q.property).le_iff_mul_eq_left hr).mp (hub q q.property)
    rw [heq] at hm
    exact predual_tendsto_unique e hm ht
  · intro a ha
    have hm := HochschildSakai.predual_tendsto_mul_right e a ht
    have heq : (fun q : S => (q : M) * a) = (fun _ : S => (0 : M)) := by
      funext q
      exact ha q q.property
    rw [heq] at hm
    exact predual_tendsto_unique e hm (predual_tendsto_const e 0 (U : Filter S))

theorem exists_central_projection_chain_supremum
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (S : Set M) (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hproj : ∀ q ∈ S, IsStarProjection q)
    (hcentral : ∀ q ∈ S, ∀ a : M, q * a = a * q) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧
      (∀ q ∈ S, q ≤ p) ∧
      (∀ r : M, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r) ∧
      (∀ a : M, (∀ q ∈ S, q * a = 0) → p * a = 0) := by
  obtain ⟨p, hp, hc, hu, hl, ha, _⟩ :=
    exists_central_projection_chain_supremum_with_limit e S hne hchain hproj hcentral
  exact ⟨p, hp, hc, hu, hl, ha⟩
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

theorem exists_orthogonal_projection_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ P : M, IsStarProjection P ∧ (∀ i, p i ≤ P) ∧
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) ∧
      PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P := by
  classical
  let f (s : Finset I) : M := ∑ i ∈ s, p i
  have hf (s : Finset I) : IsStarProjection (f s) := orthogonal_projection_finset_sum p hp horth s
  have hfm : Monotone f := by
    intro s t hst
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  obtain ⟨P, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e f hfm
    1 zero_le_one (fun s => (hf s).norm_le _)
  have hfixed (s : Finset I) : f s * P = f s := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (f s) ht
    have heq : (fun t => f s * f t) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [eventually_ge_atTop s] with t hst
      exact ((hf s).le_iff_mul_eq_left (hf t)).mp (hfm hst)
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hP : IsStarProjection P := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e P ht
      have heq : (fun s => f s * P) = f := funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hm := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun s => star (f s)) = f := funext fun s => (hf s).isSelfAdjoint.star_eq
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
  refine ⟨P, hP, ?_, ?_, ht⟩
  · intro i
    have h := hlub.1 (Set.mem_range_self ({i} : Finset I))
    simpa only [f, Finset.sum_singleton] using h
  · intro r hr hpr
    apply hlub.2
    rintro _ ⟨s, rfl⟩
    apply ((hf s).le_iff_mul_eq_right hr).mpr
    change r * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hp i).le_iff_mul_eq_right hr).mp (hpr i)

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

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma central_annihilator_chain (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ q ∈ c, CentralProjection q ∧ q * p = 0) :
    ∃ s : M, CentralProjection s ∧ s * p = 0 ∧ ∀ q ∈ c, q ≤ s := by
  obtain ⟨s, hsp, hsc, hub, _hleast, hann⟩ :=
    exists_central_projection_chain_supremum e c hne hc
      (fun q hq => (hs q hq).1.1) (fun q hq a => ((hs q hq).1.2 a).eq)
  exact ⟨s, ⟨hsp, fun a => hsc a⟩, hann p (fun q hq => (hs q hq).2), hub⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_central_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) : ∃ z : M, IsCentralSupport p z := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain a ha => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p C hchain ⟨a, ha⟩
      (fun q hq => hC hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs := hm.1.1
  have hsp := hm.1.2
  let z := 1 - s
  have hz : CentralProjection z :=
    ⟨hs.1.one_sub, fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  refine ⟨z, hz, (hp.le_iff_mul_eq_right hz.1).mpr ?_, ?_⟩
  · change (1 - s) * p = p
    rw [sub_mul, one_mul, hsp, sub_zero]
  · intro c hc hcp
    let t := z * c
    have ht : CentralProjection t :=
      ⟨hz.1.mul hc.1 (hz.2 c), fun a => (hz.2 a).mul_left (hc.2 a)⟩
    have hst : s * t = 0 := by
      change s * ((1 - s) * c) = 0
      rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
    have htp : t * p = 0 := by
      change z * c * p = 0
      rw [mul_assoc, hcp, mul_zero]
    have hnew : s + t ∈ S :=
      ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
        by rw [add_mul, hsp, htp, zero_add]⟩
    have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
    have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hm.2 hnew hle) hle)
    exact (hc.2 z).eq.trans ht0
end KadisonRingrose
end BoundedHochschild
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
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder N] [StarOrderedRing N] in
lemma cstar_finite_sum_apply {I : Type*} [Fintype I] {n : ℕ}
    (f : I → CStarMatrix (Fin n) (Fin n) N) (i j : Fin n) :
    (∑ t, f t) i j = ∑ t, f t i j := by
  classical
  exact Matrix.sum_apply i j Finset.univ (fun t => CStarMatrix.ofMatrix.symm (f t))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma completelyBounded_sum {I : Type*} [Fintype I]
    (T : I → M →L[ℂ] M) (C : I → ℝ) (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    CompletelyBoundedEstimate (∑ i, T i) (∑ i, C i) := by
  classical
  refine ⟨Finset.sum_nonneg (fun i _ => (hT i).1), fun n A => ?_⟩
  have he : A.map (∑ i, T i : M →L[ℂ] M) = ∑ i, A.map (T i) := by
    ext j k
    simp only [CStarMatrix.map_apply, sum_apply, cstar_finite_sum_apply]
  rw [he]
  exact (norm_sum_le _ _).trans (by
    simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _ => (hT i).2 n A))

def leftSandwichMap (a b : M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M a).comp (T.comp (ContinuousLinearMap.mul ℂ M b))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma leftSandwichMap_apply (a b : M) (T : M →L[ℂ] M) (x : M) :
    leftSandwichMap a b T x = a * T (b * x) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrix_scalar_mul_apply {n : ℕ} (a : M) (A : CStarMatrix (Fin n) (Fin n) M)
    (i j : Fin n) : (matrixScalarHom n a * A) i j = a * A i j := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, ite_mul, zero_mul]
  simp

lemma completelyBounded_leftSandwich (a b : M) {T : M →L[ℂ] M} {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (leftSandwichMap a b T) (‖a‖ * C * ‖b‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) hT.1) (norm_nonneg _), fun n A => ?_⟩
  have he : A.map (leftSandwichMap a b T) =
      matrixScalarHom n a * ((matrixScalarHom n b * A).map T) := by
    ext i j
    simp only [CStarMatrix.map_apply, leftSandwichMap_apply, matrix_scalar_mul_apply]
  rw [he]
  have ha : ‖matrixScalarHom n a‖ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  have hb : ‖matrixScalarHom n b‖ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  calc
    _ ≤ ‖matrixScalarHom n a‖ * ‖(matrixScalarHom n b * A).map T‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * (C * (‖b‖ * ‖A‖)) := by
      apply mul_le_mul ha _ (norm_nonneg _) (norm_nonneg _)
      exact (hT.2 n _).trans (mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) hT.1)
    _ = _ := by ring
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma finiteRightAverage_reindex (e : I ≃ J) (m : J → M) (T : M →L[ℂ] M) :
    finiteRightAverage (m ∘ e) T = finiteRightAverage m T := by
  ext a
  simpa only [finiteRightAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => T (a * m j) * star (m j))
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

lemma weakOperatorImage_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (weakOperatorImage e) := by
  intro S T h
  ext a
  apply e.symm.injective
  exact congrArg WeakDual.toStrongDual (congrFun h a)

lemma weakOperatorBall_realize (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {C : ℝ} (hC : 0 ≤ C) {F : M → WeakDual ℂ X}
    (hF : F ∈ weakOperatorBall C) :
    ∃ T : M →L[ℂ] M, ‖T‖ ≤ C ∧ weakOperatorImage e T = F := by
  let L : M →ₗ[ℂ] M :=
    { toFun := fun a => e (WeakDual.toStrongDual (F a))
      map_add' := fun a b => by
        rw [hF.1 a b]
        exact map_add e _ _
      map_smul' := fun z a => by
        rw [hF.2.1 z a]
        change e (star z • WeakDual.toStrongDual (F a)) = _
        simp only [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_star,
          RingHom.id_apply] }
  have hb (a : M) : ‖L a‖ ≤ C * ‖a‖ := by
    change ‖e (WeakDual.toStrongDual (F a))‖ ≤ _
    rw [e.norm_map]
    exact hF.2.2 a
  refine ⟨L.mkContinuous C hb, L.mkContinuous_norm_le hC hb, ?_⟩
  funext a
  change StrongDual.toWeakDual (e.symm (e (WeakDual.toStrongDual (F a)))) = F a
  rw [e.symm_apply_apply]
  rfl

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

theorem weakOperatorBall_isCompact (C : ℝ) :
    IsCompact (weakOperatorBall (M := M) (X := X) C) := by
  have hprod := isCompact_pi_infinite (fun a : M =>
    WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) (C * ‖a‖))
  apply hprod.of_isClosed_subset (weakOperatorBall_isClosed C)
  intro F hF a
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hF.2.2 a
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M X : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

def weakDualOperator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (L : M →L[ℂ] M)
    (F : WeakDual ℂ X) : WeakDual ℂ X :=
  StrongDual.toWeakDual (e.symm (L (e (WeakDual.toStrongDual F))))

lemma weakDualOperator_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (a : M) :
    weakDualOperator e L (StrongDual.toWeakDual (e.symm a)) =
      StrongDual.toWeakDual (e.symm (L a)) := by
  change StrongDual.toWeakDual (e.symm (L (e (e.symm a)))) = _
  rw [e.apply_symm_apply]

lemma weakDualOperator_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (L : M →L[ℂ] M) (hL : HasPreadjoint e L) : Continuous (weakDualOperator e L) := by
  apply WeakDual.continuous_of_continuous_eval
  intro x
  obtain ⟨y, hy⟩ := hL x
  have h : (fun F : WeakDual ℂ X => weakDualOperator e L F x) = fun F => F y := by
    funext F
    simp only [weakDualOperator, StrongDual.toWeakDual_apply, hy, e.symm_apply_apply,
      WeakDual.toStrongDual_apply]
  rw [h]
  exact WeakDual.eval_continuous y
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

lemma finiteRightAverage_mem_orbit {I : Type*} [Fintype I]
    (m : I → M) (hm : ∑ i, m i * star (m i) = 1) (T : M →L[ℂ] M) :
    finiteRightAverage m T ∈ rightAverageOrbit T := by
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, m ∘ e.symm, ?_, ?_⟩
  · exact (e.symm.sum_comp (fun i => m i * star (m i))).trans hm
  · exact (finiteRightAverage_reindex e.symm m T).symm

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem weakRightAverageOrbit_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : IsCompact (weakRightAverageOrbit e T) :=
  (weakOperatorBall_isCompact C).of_isClosed_subset isClosed_closure
    (weakRightAverageOrbit_subset_ball e hno T hT)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma leftSandwichMap_rightAverage {I : Type*} [Fintype I]
    (a b : M) (m : I → M) (T : M →L[ℂ] M) :
    leftSandwichMap a b (finiteRightAverage m T) =
      finiteRightAverage m (leftSandwichMap a b T) := by
  ext x
  simp only [leftSandwichMap_apply, finiteRightAverage_apply, Finset.mul_sum, mul_assoc]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakLeftSandwich (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M)
    (F : M → WeakDual ℂ X) : M → WeakDual ℂ X :=
  fun x => weakDualOperator e (ContinuousLinearMap.mul ℂ M a) (F (b * x))

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakLeftSandwich_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a b : M) (T : M →L[ℂ] M) :
    weakLeftSandwich e a b (weakOperatorImage e T) =
      weakOperatorImage e (leftSandwichMap a b T) := by
  funext x
  exact weakDualOperator_image e _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakLeftSandwich_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a b : M) :
    Continuous (weakLeftSandwich e a b) := by
  apply continuous_pi
  intro x
  exact (weakDualOperator_continuous e _
    ((HochschildSakai.abstract_multiplication_normal e).1 a)).comp (continuous_apply (b*x))

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakLeftSandwich_mapsTo_orbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (a b : M) (T : M →L[ℂ] M) :
    Set.MapsTo (weakLeftSandwich e a b) (weakRightAverageOrbit e T)
      (weakRightAverageOrbit e (leftSandwichMap a b T)) := by
  apply Set.MapsTo.closure _ (weakLeftSandwich_continuous e a b)
  rintro F ⟨S, ⟨n, m, hm, rfl⟩, rfl⟩
  rw [weakLeftSandwich_image, leftSandwichMap_rightAverage]
  exact ⟨_, finiteRightAverage_mem_orbit m hm _, rfl⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}

def encodeMapFamily (c : Fin n → PartialIso M) (T : Fin n → M →L[ℂ] M) : M →L[ℂ] M :=
  ∑ i, leftSandwichMap (c i : M) (star (c i : M)) (T i)

omit [PartialOrder M] [StarOrderedRing M] in
lemma extract_encodeMapFamily (c : Fin n → PartialIso M)
    (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (T : Fin n → M →L[ℂ] M) (j : Fin n) :
    leftSandwichMap (star (c j : M)) (c j : M) (encodeMapFamily c T) = T j := by
  ext x
  simp only [leftSandwichMap_apply, encodeMapFamily, sum_apply]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · simp only [← mul_assoc, column_star_mul c hi ho, ite_true, one_mul]
  · intro i _ hij
    rw [← mul_assoc, column_star_mul c hi ho j i]
    simp only [Ne.symm hij, ite_false, zero_mul]
  · intro h
    exact (h (Finset.mem_univ j)).elim

lemma encodeMapFamily_completelyBounded (c : Fin n → PartialIso M)
    (T : Fin n → M →L[ℂ] M) (C : Fin n → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    CompletelyBoundedEstimate (encodeMapFamily c T)
      (∑ i, ‖(c i : M)‖ * C i * ‖star (c i : M)‖) :=
  completelyBounded_sum _ _ (fun i => completelyBounded_leftSandwich _ _ (hT i))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def centralSupportRow (z : M) (S : Set (PartialIso M)) : Option S → M
  | none => 1 - z
  | some v => star (v.val : M)

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralSupportRow_square (z : M) (hz : IsStarProjection z)
    (S : Set (PartialIso M)) (i : Option S) :
    centralSupportRow z S i * star (centralSupportRow z S i) =
      Option.elim i (1 - z) (fun v => v.val.initial) := by
  cases i with
  | none =>
      change (1 - z) * star (1 - z) = 1 - z
      rw [hz.one_sub.isSelfAdjoint.star_eq, hz.one_sub.isIdempotentElem.eq]
  | some v => simp only [centralSupportRow, star_star, PartialIso.initial, Option.elim_some]

theorem centralSupportRow_normalized (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {z : M} (hz : IsStarProjection z) (S : Set (PartialIso M))
    (hvz : ∀ v ∈ S, v.initial ≤ z)
    (horth : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → v.initial * w.initial = 0)
    (ht : PredualTendsto e (fun s : Finset S => ∑ v ∈ s, v.val.initial) atTop z) :
    (∀ s : Finset (Option S),
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i) ≤ 1) ∧
    PredualTendsto e (fun s : Finset (Option S) =>
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i)) atTop 1 := by
  classical
  let q : Option S → M := fun i => Option.elim i (1 - z) (fun v => v.val.initial)
  have hq (i : Option S) : IsStarProjection (q i) := by
    cases i with
    | none => exact hz.one_sub
    | some v => exact v.val.initial_proj
  have ho (i j : Option S) (hij : i ≠ j) : q i * q j = 0 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some v =>
        change (1 - z) * v.val.initial = 0
        rw [sub_mul, one_mul, (v.val.initial_proj.le_iff_mul_eq_right hz).mp
          (hvz v v.property), sub_self]
    | some v =>
      cases j with
      | none =>
        change v.val.initial * (1 - z) = 0
        rw [mul_sub, mul_one, (v.val.initial_proj.le_iff_mul_eq_left hz).mp
          (hvz v v.property), sub_self]
      | some w =>
          exact horth v v.property w w.property
            (fun h => hij (congrArg some (Subtype.ext h)))
  obtain ⟨Q, hQ, hiQ, _, htQ⟩ := exists_orthogonal_projection_sum e q hq ho
  have hzQ : z ≤ Q := by
    apply (hz.le_iff_mul_eq_left hQ).mpr
    have hh := orthogonal_projection_sum_annihilator e (fun v : S => v.val.initial)
      (1 - Q) z ht (fun v => by
        rw [mul_sub, mul_one, (v.val.initial_proj.le_iff_mul_eq_left hQ).mp
          (hiQ (some v)), sub_self])
    rw [mul_sub, mul_one, sub_eq_zero] at hh
    exact hh.symm
  have hQ1 : Q = 1 := by
    have hzfix := (hz.le_iff_mul_eq_right hQ).mp hzQ
    have hcfix := (hz.one_sub.le_iff_mul_eq_right hQ).mp (hiQ none)
    have he : Q * (z + (1 - z)) = z + (1 - z) := by rw [mul_add, hzfix, hcfix]
    simpa only [add_sub_cancel, mul_one] using he
  have he (i : Option S) := centralSupportRow_square z hz S i
  constructor
  · intro s
    simpa only [he] using (orthogonal_projection_finset_sum q hq ho s).le_one
  · simpa only [he, hQ1] using htQ
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma norm_sum_inner_sq_le (x y : I → K) :
    ‖∑ i, inner ℂ (x i) (y i)‖ ^ 2 ≤
      (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 := by
  have h : ‖∑ i, inner ℂ (x i) (y i)‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_inner_le_norm (x i) (y i))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Classical

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normalGNSRepresentation_coefficients (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (η ξ : NormalGNS e) : coefficient (normalGNSRepresentation e) η ξ ∈ normalDual e := by
  have h := (mem_normalVectors e universalGNSRepresentation ξ).mp ξ.property (η : UniversalGNS M)
  exact h
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder M] [StarOrderedRing M] in
theorem representedRightAverage_factorization (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : M →L[ℂ] M) (L W : H →L[ℂ] K)
    (hT : ∀ a, σ (T a) = L.adjoint.comp ((π a).comp W)) (m : I → M) (a : M) :
    σ (finiteRightAverage m T a) =
      L.adjoint.comp ((π a).comp (representedRightAverage π σ m W)) := by
  rw [finiteRightAverage_apply, map_sum]
  simp only [map_mul, map_star, hT]
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [sum_apply, ContinuousLinearMap.comp_apply, representedRightAverage,
    operatorRowAverage_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakFactorValue (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : M) (W : H →WOT[ℂ] K) : H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM (L.adjoint.comp ((π a).comp W.toCLM))

lemma weakFactorValue_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (a : M) : Continuous (weakFactorValue π L a) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  have he : (fun W : H →WOT[ℂ] K => inner ℂ η (weakFactorValue π L a W ξ)) =
      fun W => inner ℂ ((π a).adjoint (L η)) (W ξ) := by
    funext W
    change inner ℂ η (L.adjoint ((π a) (W ξ))) = _
    rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
  rw [he]
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_id _ _
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M I J H K : Type*} [CStarAlgebra M] [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representedRightAverage_reindex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : I ≃ J) (m : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ (m ∘ e) W = representedRightAverage π σ m W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simpa only [representedRightAverage, operatorRowAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => π (m j) (W ((σ (m j)).adjoint ξ)))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma sum_norm_adjoint_sq_le (a : I → (H →L[ℂ] H))
    (ha : ∑ i, a i * star (a i) ≤ 1) (ξ : H) :
    ∑ i, ‖(a i).adjoint ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr ha)).re_inner_nonneg_right ξ
  have he : (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) =
      inner ℂ ξ ((∑ i, a i * star (a i)) ξ) := by
    rw [sum_apply, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ContinuousLinearMap.adjoint_inner_left (a i) ((a i).adjoint ξ) ξ
  have hr := congrArg Complex.re he
  change Complex.re (∑ i, inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ)) = _ at hr
  simp only [Complex.re_sum] at hr
  change (∑ i, RCLike.re (inner ℂ ((a i).adjoint ξ) ((a i).adjoint ξ))) = _ at hr
  simp only [inner_self_eq_norm_sq] at hr
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub,
    inner_self_eq_norm_sq] at hp
  change 0 ≤ ‖ξ‖ ^ 2 - Complex.re (inner ℂ ξ ((∑ i, a i * star (a i)) ξ)) at hp
  linarith

lemma norm_sum_row_apply_sq_le (a : I → (K →L[ℂ] K))
    (ha : ∑ i, a i * star (a i) ≤ 1) (y : I → K) :
    ‖∑ i, a i (y i)‖ ^ 2 ≤ ∑ i, ‖y i‖ ^ 2 := by
  let ζ := ∑ i, a i (y i)
  have he : inner ℂ ζ ζ = ∑ i, inner ℂ ((a i).adjoint ζ) (y i) := by
    conv_lhs => rhs; rw [show ζ = ∑ i, a i (y i) from rfl]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (ContinuousLinearMap.adjoint_inner_left (a i) (y i) ζ).symm
  have hi := norm_sum_inner_sq_le (fun i => (a i).adjoint ζ) y
  rw [← he, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg ζ)] at hi
  have hs := sum_norm_adjoint_sq_le a ha ζ
  have hnonneg : 0 ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hf : (‖ζ‖ ^ 2) ^ 2 ≤ ‖ζ‖ ^ 2 * ∑ i, ‖y i‖ ^ 2 :=
    hi.trans (mul_le_mul_of_nonneg_right hs hnonneg)
  change ‖ζ‖ ^ 2 ≤ _
  nlinarith [sq_nonneg (‖ζ‖ ^ 2 - ∑ i, ‖y i‖ ^ 2)]

lemma operatorRowAverage_apply_sq_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    ‖operatorRowAverage a b W ξ‖ ^ 2 ≤
      ‖W‖ ^ 2 * ∑ i, ‖(b i).adjoint ξ‖ ^ 2 := by
  rw [operatorRowAverage_apply]
  refine (norm_sum_row_apply_sq_le a ha _).trans ?_
  calc
    _ ≤ ∑ i, (‖W‖ * ‖(b i).adjoint ξ‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2
    _ = _ := by simp only [mul_pow, Finset.mul_sum]

lemma operatorRowAverage_norm_le_of_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H)) (ha : ∑ i, a i * star (a i) ≤ 1)
    (hb : ∑ i, b i * star (b i) ≤ 1) (W : H →L[ℂ] K) :
    ‖operatorRowAverage a b W‖ ≤ ‖W‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
  intro ξ
  have h := (operatorRowAverage_apply_sq_le a b ha W ξ).trans
    (mul_le_mul_of_nonneg_left (sum_norm_adjoint_sq_le b hb ξ) (sq_nonneg ‖W‖))
  rw [← mul_pow] at h
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg W) (norm_nonneg ξ))).mp h
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma summable_row_vectors (a : I → (K →L[ℂ] K))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (y : I → K) (hy : Summable (fun i => ‖y i‖ ^ 2)) :
    Summable (fun i => a i (y i)) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hy (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨s, fun t ht => ?_⟩
  have h := norm_sum_row_apply_sq_le (fun i : t => a i)
    (by rw [Finset.sum_coe_sort t (fun i => a i * star (a i))]; exact ha t) (fun i : t => y i)
  rw [Finset.sum_coe_sort t (fun i => a i (y i)),
    Finset.sum_coe_sort t (fun i => ‖y i‖ ^ 2)] at h
  have hpos : 0 ≤ ∑ i ∈ t, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hh := hs t ht
  rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hh
  have hsq := h.trans_lt hh
  nlinarith [norm_nonneg (∑ i ∈ t, a i (y i))]

lemma summable_adjoint_row_sq (b : I → (H →L[ℂ] H))
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1) (ξ : H) :
    Summable (fun i => ‖(b i).adjoint ξ‖ ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := ‖ξ‖ ^ 2)
  intro s
  rw [← Finset.sum_coe_sort s (fun i => ‖(b i).adjoint ξ‖ ^ 2)]
  exact sum_norm_adjoint_sq_le (fun i : s => b i)
      (by rw [Finset.sum_coe_sort s (fun i => b i * star (b i))]; exact hb s) ξ

lemma summable_operator_row_apply (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    Summable (fun i => a i (W ((b i).adjoint ξ))) := by
  apply summable_row_vectors a ha
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => pow_le_pow_left₀ (norm_nonneg _) (W.le_opNorm _) 2)
  simpa only [mul_pow] using (summable_adjoint_row_sq b hb ξ).mul_left (‖W‖ ^ 2)

lemma tsum_operator_row_apply_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    ‖∑' i, a i (W ((b i).adjoint ξ))‖ ≤ ‖W‖ * ‖ξ‖ := by
  have ht := (summable_operator_row_apply a b ha hb W ξ).hasSum.norm
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro s
  have h := (operatorRowAverage_norm_le_of_le (fun i : s => a i) (fun i : s => b i)
    (by rw [Finset.sum_coe_sort s (fun i => a i * star (a i))]; exact ha s)
    (by rw [Finset.sum_coe_sort s (fun i => b i * star (b i))]; exact hb s) W)
  have h' := (operatorRowAverage (fun i : s => a i) (fun i : s => b i) W).le_opNorm ξ
  rw [operatorRowAverage_apply,
    Finset.sum_coe_sort s (fun i => a i (W ((b i).adjoint ξ)))] at h'
  exact h'.trans (mul_le_mul_of_nonneg_right h (norm_nonneg ξ))

def infiniteOperatorRow (a : I → (K →L[ℂ] K)) (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  LinearMap.mkContinuous
    { toFun := fun ξ => ∑' i, a i (W ((b i).adjoint ξ))
      map_add' := by
        intro ξ η
        simp only [map_add]
        exact (summable_operator_row_apply a b ha hb W ξ).tsum_add
          (summable_operator_row_apply a b ha hb W η)
      map_smul' := by
        intro c ξ
        simp only [map_smul, RingHom.id_apply]
        exact tsum_const_smul'' c }
    ‖W‖ (tsum_operator_row_apply_norm_le a b ha hb W)

lemma infiniteOperatorRow_norm_le (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) : ‖infiniteOperatorRow a b ha hb W‖ ≤ ‖W‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W)
    (tsum_operator_row_apply_norm_le a b ha hb W)

lemma infiniteOperatorRow_hasSum (a : I → (K →L[ℂ] K))
    (b : I → (H →L[ℂ] H))
    (ha : ∀ s : Finset I, ∑ i ∈ s, a i * star (a i) ≤ 1)
    (hb : ∀ s : Finset I, ∑ i ∈ s, b i * star (b i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    HasSum (fun i => a i (W ((b i).adjoint ξ))) (infiniteOperatorRow a b ha hb W ξ) :=
  (summable_operator_row_apply a b ha hb W ξ).hasSum
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def rowDefect (m : I → M) (s : Finset I) : M :=
  CFC.sqrt (1 - ∑ i ∈ s, m i * star (m i))

lemma rowDefect_nonneg (m : I → M) (s : Finset I) : 0 ≤ rowDefect m s :=
  CFC.sqrt_nonneg _

lemma rowDefect_mul_star (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) :
    rowDefect m s * star (rowDefect m s) = 1 - ∑ i ∈ s, m i * star (m i) := by
  rw [(rowDefect_nonneg m s).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hs)

lemma rowDefect_norm_le (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) : ‖rowDefect m s‖ ≤ 1 := by
  have hd : ‖1 - ∑ i ∈ s, m i * star (m i)‖ ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hs)).mpr
    exact sub_le_self _ (Finset.sum_nonneg fun i _ => mul_star_self_nonneg (m i))
  rw [← rowDefect_mul_star m s hs, CStarRing.norm_self_mul_star] at hd
  nlinarith [norm_nonneg (rowDefect m s)]

def completedRow (m : I → M) (s : Finset I) : Option s → M
  | none => rowDefect m s
  | some i => m i

lemma completedRow_normalized (m : I → M) (s : Finset I)
    (hs : ∑ i ∈ s, m i * star (m i) ≤ 1) :
    ∑ i, completedRow m s i * star (completedRow m s i) = 1 := by
  classical
  rw [Fintype.sum_option]
  change rowDefect m s * star (rowDefect m s) + ∑ i : s, m i * star (m i) = 1
  rw [rowDefect_mul_star m s hs, Finset.sum_coe_sort s (fun i => m i * star (m i))]
  exact sub_add_cancel _ _

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma completedRow_average (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (s : Finset I) (W : H →L[ℂ] K) :
    representedRightAverage π σ (completedRow m s) W =
      (π (rowDefect m s)).comp (W.comp (σ (rowDefect m s)).adjoint) +
      ∑ i ∈ s, (π (m i)).comp (W.comp (σ (m i)).adjoint) := by
  classical
  unfold representedRightAverage operatorRowAverage
  rw [Fintype.sum_option]
  change _ + (∑ i : s, (π (m i)).comp (W.comp (σ (m i)).adjoint)) = _
  rw [Finset.sum_coe_sort s (fun i => (π (m i)).comp (W.comp (σ (m i)).adjoint))]
  rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder M] [StarOrderedRing M] in
lemma represented_norm_sq (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (d : M) (ξ : H) :
    ‖σ d ξ‖ ^ 2 = RCLike.re (inner ℂ ξ (σ (star d * d) ξ)) := by
  rw [map_mul, map_star]
  change _ = RCLike.re (inner ℂ ξ ((σ d).adjoint (σ d ξ)))
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

lemma rowDefect_strong_zero (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (ξ : H) :
    Tendsto (fun s : Finset I => σ (rowDefect m s) ξ) atTop (𝓝 0) := by
  have he (s : Finset I) : ‖σ (rowDefect m s) ξ‖ ^ 2 =
      ‖ξ‖ ^ 2 - RCLike.re (inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ)) := by
    have hd := rowDefect_mul_star m s (hm s)
    rw [(rowDefect_nonneg m s).isSelfAdjoint.star_eq] at hd
    rw [represented_norm_sq, (rowDefect_nonneg m s).isSelfAdjoint.star_eq, hd,
      map_sub, map_one]
    simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub, inner_self_eq_norm_sq]
  have hs : Tendsto (fun s : Finset I => ‖σ (rowDefect m s) ξ‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [he]
    have h := (tendsto_const_nhds (x := ‖ξ‖ ^ 2)).sub ((RCLike.continuous_re.tendsto _).comp (hlim ξ))
    simpa only [Function.comp_apply, inner_self_eq_norm_sq, sub_self] using h
  have hn : Tendsto (fun s : Finset I => ‖σ (rowDefect m s) ξ‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hs
    change Tendsto (fun s : Finset I => Real.sqrt (‖σ (rowDefect m s) ξ‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

lemma rowDefect_average_strong_zero (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (W : H →L[ℂ] K) (ξ : H) :
    Tendsto (fun s : Finset I =>
      π (rowDefect m s) (W ((σ (rowDefect m s)).adjoint ξ))) atTop (𝓝 0) := by
  have he (s : Finset I) : (σ (rowDefect m s)).adjoint = σ (rowDefect m s) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      (rowDefect_nonneg m s).isSelfAdjoint.star_eq]
  simp_rw [he]
  have hn : Tendsto (fun s : Finset I => ‖W‖ * ‖σ (rowDefect m s) ξ‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (tendsto_const_nhds.mul
      ((rowDefect_strong_zero σ m hm hlim ξ).norm))
  refine squeeze_zero_norm (fun s => ?_) hn
  calc
    _ ≤ ‖π (rowDefect m s)‖ * ‖W (σ (rowDefect m s) ξ)‖ := (π _).le_opNorm _
    _ ≤ 1 * (‖W‖ * ‖σ (rowDefect m s) ξ‖) :=
      mul_le_mul ((NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (rowDefect_norm_le m s (hm s)))
        (W.le_opNorm _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representation_row_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1) (s : Finset I) :
    ∑ i ∈ s, π (m i) * star (π (m i)) ≤ 1 := by
  simpa only [map_sum, map_mul, map_star, map_one] using OrderHomClass.mono π (hm s)

def infiniteRepresentedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  infiniteOperatorRow (fun i => π (m i)) (fun i => σ (m i))
    (representation_row_le π m hm) (representation_row_le σ m hm) W

lemma infiniteRepresentedRightAverage_norm_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1) (W : H →L[ℂ] K) :
    ‖infiniteRepresentedRightAverage π σ m hm W‖ ≤ ‖W‖ :=
  infiniteOperatorRow_norm_le _ _ _ _ W

lemma infiniteRepresentedRightAverage_hasSum (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    HasSum (fun i => π (m i) (W ((σ (m i)).adjoint ξ)))
      (infiniteRepresentedRightAverage π σ m hm W ξ) :=
  infiniteOperatorRow_hasSum _ _ _ _ W ξ

lemma completedRow_average_tendsto (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (W : H →L[ℂ] K) (ξ : H) :
    Tendsto (fun s : Finset I => representedRightAverage π σ (completedRow m s) W ξ)
      atTop (𝓝 (infiniteRepresentedRightAverage π σ m hm W ξ)) := by
  have hd := rowDefect_average_strong_zero π σ m hm hlim W ξ
  have hs := infiniteRepresentedRightAverage_hasSum π σ m hm W ξ
  have he (s : Finset I) : representedRightAverage π σ (completedRow m s) W ξ =
      π (rowDefect m s) (W ((σ (rowDefect m s)).adjoint ξ)) +
      ∑ i ∈ s, π (m i) (W ((σ (m i)).adjoint ξ)) := by
    rw [completedRow_average]
    simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  simp_rw [he]
  simpa only [zero_add] using hd.add hs
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma infinite_represented_average_mem_family
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (F : Set (H →WOT[ℂ] K)) (hclosed : IsClosed F)
    (hinv : RepresentedRightAverageInvariant π σ F) (W : H →WOT[ℂ] K) (hW : W ∈ F)
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) :
    ContinuousLinearMapWOT.ofCLM (infiniteRepresentedRightAverage π σ m hm W.toCLM) ∈ F := by
  classical
  have ht : Tendsto (fun s : Finset I => weakRepresentedRightAverage π σ (completedRow m s) W)
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM
        (infiniteRepresentedRightAverage π σ m hm W.toCLM))) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    exact tendsto_const_nhds.inner (completedRow_average_tendsto π σ m hm hlim W.toCLM ξ)
  apply hclosed.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  let q := Fintype.equivFin (Option s)
  let r := completedRow m s
  have hr : ∑ i, r i * star (r i) = 1 := completedRow_normalized m s (hm s)
  have hq : ∑ i, r (q.symm i) * star (r (q.symm i)) = 1 :=
    (q.symm.sum_comp (fun i => r i * star (r i))).trans hr
  have hin := hinv (Fintype.card (Option s)) (r ∘ q.symm) hq hW
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_reindex π σ q.symm r W.toCLM)
  change weakRepresentedRightAverage π σ (r ∘ q.symm) W =
    weakRepresentedRightAverage π σ r W at he
  rwa [he] at hin
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma centralSupportRow_compression_term
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    {p z : M} (hp : IsStarProjection p) (hz : IsStarProjection z) (hpz : p ≤ z)
    (S : Set (PartialIso M)) (hS : ∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z)
    (W : H →L[ℂ] K) (i : Option S) (ξ : H) :
    π (centralSupportRow z S i) (W ((σ (centralSupportRow z S i)).adjoint (σ z ξ))) =
      π (centralSupportRow z S i)
        (π p (W (σ p ((σ (centralSupportRow z S i)).adjoint ξ)))) := by
  cases i with
  | none =>
      have hright : (σ (1 - z)).adjoint.comp (σ z) = 0 := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
          hz.one_sub.isSelfAdjoint.star_eq]
        change σ (1 - z) * σ z = 0
        rw [← map_mul, hz.one_sub_mul_self, map_zero]
      have hleft : (π (1 - z)).comp (π p) = 0 := by
        change π (1 - z) * π p = 0
        rw [← map_mul, sub_mul, one_mul, (hp.le_iff_mul_eq_right hz).mp hpz,
          sub_self, map_zero]
      have hr := congrArg (fun A : H →L[ℂ] H => A ξ) hright
      have hl := congrArg (fun A : K →L[ℂ] K => A (W (σ p ((σ (1-z)).adjoint ξ)))) hleft
      change (σ (1 - z)).adjoint (σ z ξ) = 0 at hr
      change π (1 - z) (π p (W (σ p ((σ (1-z)).adjoint ξ)))) = 0 at hl
      change π (1 - z) (W ((σ (1-z)).adjoint (σ z ξ))) = _
      rw [hr, map_zero, map_zero]
      exact hl.symm
  | some v =>
      have hpv : p * (v.val : M) = v.val := by
        calc
          _ = p * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = v.val := by rw [← mul_assoc,
            (v.val.final_proj.le_iff_mul_eq_right hp).mp (hS v v.property).1,
            v.val.final_mul]
      have hvz : (v.val : M) * z = v.val := by
        calc
          _ = ((v.val : M) * v.val.initial) * z := by rw [v.val.mul_initial]
          _ = v.val := by rw [mul_assoc,
            (v.val.initial_proj.le_iff_mul_eq_left hz).mp (hS v v.property).2,
            v.val.mul_initial]
      have hvp : star (v.val : M) * p = star (v.val : M) := by
        simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpv
      have hσ (a b c : M) (h : a * b = c) (η : H) : σ a (σ b η) = σ c η :=
        congrArg (fun A : H →L[ℂ] H => A η) ((map_mul σ a b).symm.trans (congrArg σ h))
      have hπ (a b c : M) (h : a * b = c) (η : K) : π a (π b η) = π c η :=
        congrArg (fun A : K →L[ℂ] K => A η) ((map_mul π a b).symm.trans (congrArg π h))
      have hs : (σ (star (v.val : M))).adjoint = σ (v.val : M) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
      simp only [centralSupportRow, hs, hσ _ _ _ hvz, hσ _ _ _ hpv, hπ _ _ _ hvp]

theorem centralSupportRow_compression_norm_le
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    {p z : M} (hp : IsStarProjection p) (hz : IsStarProjection z) (hpz : p ≤ z)
    (S : Set (PartialIso M)) (hS : ∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z)
    (hm : ∀ s : Finset (Option S),
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i) ≤ 1)
    (W : H →L[ℂ] K) :
    ‖(infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W).comp (σ z)‖ ≤
      ‖(π p).comp (W.comp (σ p))‖ := by
  have he : (infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W).comp (σ z) =
      infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm
        ((π p).comp (W.comp (σ p))) := by
    ext ξ
    have h₁ := infiniteRepresentedRightAverage_hasSum π σ (centralSupportRow z S) hm W (σ z ξ)
    have h₂ := infiniteRepresentedRightAverage_hasSum π σ (centralSupportRow z S) hm
      ((π p).comp (W.comp (σ p))) ξ
    have hf := funext (fun i => centralSupportRow_compression_term π σ hp hz hpz S hS W i ξ)
    simp only [ContinuousLinearMap.comp_apply] at h₂ ⊢
    rw [hf] at h₁
    exact h₁.unique h₂
  rw [he]
  exact infiniteRepresentedRightAverage_norm_le π σ (centralSupportRow z S) hm _
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def normalGNSWeak (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : WeakDual ℂ X) :
    NormalGNS e →WOT[ℂ] NormalGNS e :=
  ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (e (WeakDual.toStrongDual F)))

lemma normalGNSWeak_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (normalGNSWeak e) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro ξ η
  obtain ⟨x, hx⟩ := (mem_normalDual e _).mp (normalGNSRepresentation_coefficients e η ξ)
  have heq : (fun F : WeakDual ℂ X => inner ℂ η (normalGNSWeak e F ξ)) =
      fun F => star (F x) := by
    funext F
    change coefficient (normalGNSRepresentation e) η ξ (e (WeakDual.toStrongDual F)) = _
    rw [hx, e.symm_apply_apply]
    rfl
  rw [heq]
  exact (WeakDual.eval_continuous x).star
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normalGNS_factorization [Nontrivial M] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    Nonempty (OperatorFactorization
      ((normalGNSRepresentation e).toLinearMap.comp T.toLinearMap) C) := by
  let := normalGNS_nontrivial e
  exact represented_factorization (normalGNSRepresentation e) T hC hT
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normalGNS_predual_tendsto (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {I : Type*} {l : Filter I} {a : I → M} {b : M} (h : PredualTendsto e a l b)
    (ξ η : NormalGNS e) :
    Tendsto (fun i => inner ℂ η (normalGNSRepresentation e (a i) ξ)) l
      (𝓝 (inner ℂ η (normalGNSRepresentation e b ξ))) := by
  obtain ⟨x, hx⟩ := (mem_normalDual e _).mp (normalGNSRepresentation_coefficients e η ξ)
  change Tendsto (fun i => coefficient (normalGNSRepresentation e) η ξ (a i)) l
    (𝓝 (coefficient (normalGNSRepresentation e) η ξ b))
  simpa only [hx] using (h x).star
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma normalGNS_row_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (m : I → M)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1)
    (ξ : NormalGNS e) :
    Tendsto (fun s : Finset I => inner ℂ ξ
      (normalGNSRepresentation e (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ)) := by
  simpa only [map_one, one_apply_eq_self] using normalGNS_predual_tendsto e hlim ξ ξ
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem minimal_family_projection_norm (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (F : Set (NormalGNS e →WOT[ℂ] K))
    (hclosed : IsClosed F) (hconv : Convex ℝ F)
    (hinv : RepresentedRightAverageInvariant π (normalGNSRepresentation e) F)
    (hmin : ∀ G : Set (NormalGNS e →WOT[ℂ] K), G ⊆ F → G.Nonempty → IsClosed G →
      Convex ℝ G → RepresentedRightAverageInvariant π (normalGNSRepresentation e) G → F ⊆ G)
    (W : NormalGNS e →WOT[ℂ] K) (hW : W ∈ F) {p : M} (hp : IsStarProjection p) :
    ‖W.toCLM.comp (normalGNSRepresentation e p)‖ =
      ‖(π p).comp (W.toCLM.comp (normalGNSRepresentation e p))‖ := by
  let σ := normalGNSRepresentation e
  obtain ⟨z, hz⟩ := exists_central_support e hp
  obtain ⟨S, hS, ho, ht⟩ := exists_central_support_row e hp hz
  obtain ⟨hm, hlim⟩ := centralSupportRow_normalized e hz.1.1 S
    (fun v hv => (hS v hv).2) ho ht
  let U := ContinuousLinearMapWOT.ofCLM
    (infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W.toCLM)
  have hU : U ∈ F := infinite_represented_average_mem_family π σ F hclosed hinv W hW
    (centralSupportRow z S) hm (normalGNS_row_limit e _ hlim)
  have hzcomm (a : M) : (σ z).comp (σ a) = (σ a).comp (σ z) := by
    change σ z * σ a = σ a * σ z
    rw [← map_mul, ← map_mul, (hz.1.2 a).eq]
  have hn := compressed_norm_eq_on_minimal_family π σ F hclosed hconv hinv hmin
    (1 : K →L[ℂ] K) (σ z) (fun _ => by ext; simp) hzcomm hW hU
  have hn' : ‖W.toCLM.comp (σ z)‖ = ‖U.toCLM.comp (σ z)‖ := by
    have hcomp (A : NormalGNS e →L[ℂ] K) : (1 : K →L[ℂ] K).comp A = A := by
      ext ξ
      rfl
    simpa only [weakCompression, ContinuousLinearMapWOT.toCLM_comp,
      ContinuousLinearMapWOT.toCLM_ofCLM, hcomp] using hn
  have hle : ‖W.toCLM.comp (σ z)‖ ≤ ‖(π p).comp (W.toCLM.comp (σ p))‖ := by
    rw [hn']
    exact centralSupportRow_compression_norm_le π σ hp hz.1.1 hz.2.1 S hS hm W.toCLM
  have hpp : ‖(π p).comp (W.toCLM.comp (σ p))‖ ≤ ‖W.toCLM.comp (σ p)‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) ((hp.map π).norm_le _))
  have hpz : (σ z).comp (σ p) = σ p := by
    change σ z * σ p = σ p
    rw [← map_mul, (hp.le_iff_mul_eq_right hz.1.1).mp hz.2.1]
  have hpz' : W.toCLM.comp (σ p) = (W.toCLM.comp (σ z)).comp (σ p) := by
    rw [ContinuousLinearMap.comp_assoc, hpz]
  have hpc : ‖W.toCLM.comp (σ p)‖ ≤ ‖W.toCLM.comp (σ z)‖ := by
    rw [hpz']
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) ((hp.map σ).norm_le _))
  exact le_antisymm (hpc.trans hle) hpp
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma right_module_on_projections (T : M →L[ℂ] M)
    (hT : ∀ a p : M, IsStarProjection p → T a * p - T (a * p) * p = 0)
    (a p : M) (hp : IsStarProjection p) : T (a * p) = T a * p := by
  have hd := sub_eq_zero.mp (hT a p hp)
  have hc := sub_eq_zero.mp (hT (a * p) (1-p) hp.one_sub)
  have hz : a * p * (1-p) = 0 := by rw [mul_assoc, hp.mul_one_sub_self, mul_zero]
  rw [hz, map_zero, zero_mul] at hc
  calc
    T (a * p) = T (a * p) * p + T (a * p) * (1-p) := by
      rw [← mul_add, add_sub_cancel, mul_one]
    _ = T a * p := by rw [← hd, hc, add_zero]

theorem right_module_of_projection_defects (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M)
    (hT : ∀ a p : M, IsStarProjection p → T a * p - T (a * p) * p = 0) :
    ∀ a b : M, T (a * b) = T a * b := by
  intro a
  let L := T.comp (ContinuousLinearMap.mul ℂ M a) - ContinuousLinearMap.mul ℂ M (T a)
  have hspan : Submodule.span ℂ {p : M | IsStarProjection p} ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro p hp
    change T (a * p) - T a * p = 0
    rw [right_module_on_projections T hT a p hp, sub_self]
  have hclosed := Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  rw [HochschildSakai.projection_span_dense e] at hclosed
  intro b
  exact sub_eq_zero.mp (hclosed (show b ∈ (⊤ : Submodule ℂ M) from trivial))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def weakFactorFamily (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (W : H →WOT[ℂ] K) : M → (H →WOT[ℂ] H) :=
  fun a => weakFactorValue π L a W

lemma weakFactorFamily_continuous (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) :
    Continuous (weakFactorFamily π L) := by
  apply continuous_pi
  intro a
  exact weakFactorValue_continuous π L a
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def weakNormalOperatorFamily (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : M → WeakDual ℂ X) : M → (NormalGNS e →WOT[ℂ] NormalGNS e) :=
  fun a => normalGNSWeak e (F a)

lemma weakNormalOperatorFamily_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (weakNormalOperatorFamily e) := by
  apply continuous_pi
  intro a
  exact (normalGNSWeak_continuous e).comp (continuous_apply a)

lemma weakNormalOperatorFamily_image (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : M →L[ℂ] M) (a : M) :
    weakNormalOperatorFamily e (weakOperatorImage e T) a =
      ContinuousLinearMapWOT.ofCLM (normalGNSRepresentation e (T a)) := by
  change ContinuousLinearMapWOT.ofCLM
    (normalGNSRepresentation e (e (e.symm (T a)))) = _
  rw [e.apply_symm_apply]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem lifted_orbit_realization (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (hfac : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    {V : NormalGNS e →WOT[ℂ] K}
    (hV : V ∈ closedRepresentedAveragingOrbit π (normalGNSRepresentation e)
      (ContinuousLinearMapWOT.ofCLM W)) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ C ∧ weakOperatorImage e S ∈ weakRightAverageOrbit e T ∧
      ∀ a, normalGNSRepresentation e (S a) = L.adjoint.comp ((π a).comp V.toCLM) := by
  let B := weakNormalOperatorFamily e '' weakRightAverageOrbit e T
  have hBc : IsClosed B := ((weakRightAverageOrbit_isCompact e hno T hT).image
    (weakNormalOperatorFamily_continuous e)).isClosed
  have hpre : IsClosed (weakFactorFamily π L ⁻¹' B) :=
    hBc.preimage (weakFactorFamily_continuous π L)
  have hsub : representedAveragingOrbit π (normalGNSRepresentation e)
      (ContinuousLinearMapWOT.ofCLM W) ⊆ weakFactorFamily π L ⁻¹' B := by
    rintro V ⟨n, m, hm, rfl⟩
    refine ⟨weakOperatorImage e (finiteRightAverage m T),
      subset_closure ⟨finiteRightAverage m T, finiteRightAverage_mem_orbit m hm T, rfl⟩, ?_⟩
    funext a
    rw [weakNormalOperatorFamily_image]
    exact congrArg ContinuousLinearMapWOT.ofCLM
      (representedRightAverage_factorization π (normalGNSRepresentation e) T L W hfac m a)
  obtain ⟨F, hF, he⟩ := closure_minimal hsub hpre hV
  obtain ⟨S, hSC, hSF⟩ := weakOperatorBall_realize e hT.1
    (weakRightAverageOrbit_subset_ball e hno T hT hF)
  refine ⟨S, hSC, hSF ▸ hF, fun a => ?_⟩
  have hh := congrFun he a
  rw [← hSF, weakNormalOperatorFamily_image] at hh
  exact congrArg ContinuousLinearMapWOT.toCLM hh
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    (T : M →L[ℂ] M) {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ C ∧ weakOperatorImage e S ∈ weakRightAverageOrbit e T ∧
      ∀ a b : M, S (a * b) = S a * b := by
  obtain ⟨D⟩ := normalGNS_factorization e T hC hT
  let π := D.representation
  let L := D.leftMap
  let W := D.rightMap
  have hfac : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W) :=
    D.factorization
  obtain ⟨F, hFsub, hFne, hFc, hFv, hFi, hFm⟩ := exists_minimal_represented_averages
    π (normalGNSRepresentation e) (ContinuousLinearMapWOT.ofCLM W)
  obtain ⟨V, hV⟩ := hFne
  obtain ⟨S, hSC, hSorb, hSfac⟩ := lifted_orbit_realization e hno T hT π L W hfac (hFsub hV)
  refine ⟨S, hSC, hSorb, ?_⟩
  apply right_module_of_projection_defects e S
  intro a p hp
  exact projection_defect_eq_zero e π L V.toCLM S hSfac
    (fun f hf => minimal_family_projection_norm e π F hFc hFv hFi hFm V hV hf) a hp
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem exists_finite_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    {n : ℕ} (T : Fin (n+1) → M →L[ℂ] M) (C : Fin (n+1) → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    ∃ S : Fin (n+1) → M →L[ℂ] M,
      (∀ i, ‖S i‖ ≤ C i ∧ ∀ a b, S i (a*b) = S i a * b) ∧
      (fun i => weakOperatorImage e (S i)) ∈ weakFamilyAverageOrbit e T := by
  obtain ⟨c, hi, ho, _⟩ := exists_properlyInfinite_matrix_columns e hno (n+1)
  let B := encodeMapFamily c T
  let D := ∑ i, ‖(c i : M)‖ * C i * ‖star (c i : M)‖
  have hB : CompletelyBoundedEstimate B D := encodeMapFamily_completelyBounded c T C hT
  have hB' : CompletelyBoundedEstimate B (D+1) :=
    ⟨by linarith [hB.1], fun k A => (hB.2 k A).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg A))⟩
  obtain ⟨R, _, hRorb, hR⟩ := exists_right_module_average e hno B
    (by linarith [hB.1] : 0 < D+1) hB'
  let S (i : Fin (n+1)) := leftSandwichMap (star (c i : M)) (c i : M) R
  have he (i : Fin (n+1)) :
      leftSandwichMap (star (c i : M)) (c i : M) B = T i :=
    extract_encodeMapFamily c hi ho T i
  have horb (i : Fin (n+1)) : weakOperatorImage e (S i) ∈ weakRightAverageOrbit e (T i) := by
    have h := weakLeftSandwich_mapsTo_orbit e (star (c i : M)) (c i : M) B hRorb
    rwa [weakLeftSandwich_image, he] at h
  refine ⟨S, fun i => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨U, hU, hUS⟩ := weakOperatorBall_realize e (hT i).1
      (weakRightAverageOrbit_subset_ball e hno (T i) (hT i) (horb i))
    have heq := weakOperatorImage_injective e hUS
    exact heq ▸ hU
  · intro a b
    change star (c i : M) * R ((c i : M) * (a*b)) =
      (star (c i : M) * R ((c i : M) * a)) * b
    rw [← mul_assoc (c i : M) a b, hR, mul_assoc]
  · let E (F : M → WeakDual ℂ X) : Fin (n+1) → M → WeakDual ℂ X :=
      fun i => weakLeftSandwich e (star (c i : M)) (c i : M) F
    have hEc : Continuous E := continuous_pi (fun i => weakLeftSandwich_continuous e _ _)
    have hmap : Set.MapsTo E (weakOperatorImage e '' rightAverageOrbit B)
        (finiteFamilyAverageOrbit e T) := by
      rintro F ⟨U, ⟨k, m, hm, rfl⟩, rfl⟩
      refine ⟨k, m, hm, ?_⟩
      funext i
      dsimp [E]
      rw [weakLeftSandwich_image, leftSandwichMap_rightAverage, he]
    have hh := hmap.closure hEc hRorb
    simpa only [E, weakLeftSandwich_image, S, weakFamilyAverageOrbit] using hh
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.exists_finite_right_module_average.{u} := @OAI.BoundedHochschild.KadisonRingrose.exists_finite_right_module_average.{u}
