-- Prove2me | solution 1 for NumberField.TateGlobal.continuous_localChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/828cb780-5ee5-5891-850e-c6ced2d3f297

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_continuous_localChar

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_continuous_localChar.NumberField IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing place AdeleRing"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "localChar"
p2m_open "NumberField.TateGlobal NumberField"

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_continuous_localChar.NumberField.TateGlobal NumberField.AdelicLevel Topology Filter"

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
private theorem r06_cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in
private def r06_finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
private theorem r06_continuous_finSinglePrincipal : Continuous (r06_finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
private theorem r06_localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (r06_cofinite_le_principal_compl_singleton v)
          (r06_finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

private theorem r06_continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (r06_cofinite_le_principal_compl_singleton v)) ∘ (r06_finSinglePrincipal v) ∘ Units.val :=
    funext fun t => r06_localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((r06_continuous_finSinglePrincipal v).comp Units.continuous_val)

private theorem r06_continuous_emb :
    Continuous ⇑((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (r06_continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ =>
          ((((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v) t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
            : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ =>
            (((Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v) t : (AdeleRing (𝓞 F) F)ˣ)
              : AdeleRing (𝓞 F) F)) ∘ (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (r06_continuous_localUnit_val v)

end

end NumberField.TateGlobal

open _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_continuous_localChar.NumberField.TateGlobal NumberField.AdelicLevel Topology Filter in

theorem solution {K : Type} [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : Continuous ⇑χ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous ⇑(localChar χ v) := by
  show Continuous (⇑χ ∘ ⇑((Units.map (finIncl (𝓞 K) K)).comp (localUnit (𝓞 K) K v)))
  exact hχ.comp (r06_continuous_emb v)

end S_NumberField_TateGlobal_continuous_localChar
end P2MW
export P2MW.S_NumberField_TateGlobal_continuous_localChar (solution)
