-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1f898f23-93bd-5ba1-98be-888b1593c96a

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField

set_option maxHeartbeats 800000

theorem solution
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (w'' : HeightOneSpectrum (𝓞 K''))
    (h : HeightOneSpectrum.under (𝓞 K) w'' = HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w''))
    (x : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).adicCompletion K) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K' K''
        (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K') w'').Extension (𝓞 K''))
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'
        (⟨HeightOneSpectrum.under (𝓞 K') w'', rfl⟩ :
          (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K')) x) =
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
        (⟨w'', h⟩ : (HeightOneSpectrum.under (𝓞 K) (HeightOneSpectrum.under (𝓞 K') w'')).Extension (𝓞 K'')) x := by

  let w' := HeightOneSpectrum.under (𝓞 K') w''
  let w := HeightOneSpectrum.under (𝓞 K) w'
  let ι₁ := HeightOneSpectrum.Extension.adicCompletionSemialgHom K K' (⟨w', rfl⟩ : w.Extension (𝓞 K'))
  let ι₂ := HeightOneSpectrum.Extension.adicCompletionSemialgHom K' K'' (⟨w'', rfl⟩ : w'.Extension (𝓞 K''))
  let ι₃ := HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' (⟨w'', h⟩ : w.Extension (𝓞 K''))
  have hf : Continuous (fun y : w.adicCompletion K => ι₂ (ι₁ y)) :=
    (HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K' K'' _).comp
      (HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K' _)
  have hg : Continuous (fun y : w.adicCompletion K => ι₃ y) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K K'' _
  have hdense : DenseRange (fun k : WithVal (w.valuation K) => (k : w.adicCompletion K)) :=
    (HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w).denseRange.comp
      (UniformSpace.Completion.denseRange_coe (α := WithVal (w.valuation K)))
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)
  have key := hdense.equalizer hf hg (by
    funext k
    show ι₂ (ι₁ ((k : WithVal (w.valuation K)) : w.adicCompletion K)) = ι₃ ((k : WithVal (w.valuation K)) : w.adicCompletion K)
    rw [HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
    show ι₂ ((((WithVal.equiv (w'.valuation K')).symm (algebraMap K K' k.ofVal)) : WithVal (w'.valuation K')) : w'.adicCompletion K') = _
    rw [HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe, HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe]
    congr 2
    show (WithVal.equiv (HeightOneSpectrum.valuation K'' w'')).symm (algebraMap K' K'' (algebraMap K K' k.ofVal)) =
      (WithVal.equiv (HeightOneSpectrum.valuation K'' w'')).symm (algebraMap K K'' k.ofVal)
    rw [← IsScalarTower.algebraMap_apply])
  exact congrFun key x

end S_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower (solution)
