-- Prove2me | solution 1 for M4aHerbrand.Bridge.genuineBeta_comp_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b9b3e283-4875-57bb-8d9f-952f0cdfa76c

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_adicCompletionSemialgHom_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_Bridge_genuineBeta_comp_of_tower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField M4aHerbrand.Bridge

namespace F0bTower

theorem semialgHom_index_transport
    (K K'' : Type) [Field K] [NumberField K] [Field K''] [NumberField K''] [Algebra K K'']
    (w'' : HeightOneSpectrum (𝓞 K'')) (x : FiniteAdeleRing (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : HeightOneSpectrum.under (𝓞 K) w'' = v) :
    HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' (⟨w'', hv⟩ : v.Extension (𝓞 K'')) (x v) =
      HeightOneSpectrum.Extension.adicCompletionSemialgHom K K'' (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K'')) (x (HeightOneSpectrum.under (𝓞 K) w'')) := by
  subst hv
  rfl

theorem finiteConorm_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] :
    (finiteConorm (𝓞 K') K' K'' (𝓞 K'')).comp (finiteConorm (𝓞 K) K K' (𝓞 K')) = finiteConorm (𝓞 K) K K'' (𝓞 K'') := by
  refine RingHom.ext fun x => FiniteAdeleRing.ext K'' fun w'' => ?_
  rw [RingHom.comp_apply, finiteConorm_apply, finiteConorm_apply, finiteConorm_apply,
    IsDedekindDomain.HeightOneSpectrum.adicCompletionSemialgHom_comp_of_tower K K' K'' w''
      (IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers K K' K'' w'').symm]
  exact semialgHom_index_transport K K'' w'' x _ (IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers K K' K'' w'').symm

end F0bTower

namespace F0bTower

open NumberField.InfinitePlace M4aHerbrand.ArchSemilocal
open scoped NumberField.LiesOver

theorem algebraMap_completion_comp
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K'']
    (v : InfinitePlace K) (w' : InfinitePlace K') (w : InfinitePlace K'')
    [w'.1.LiesOver v.1] [w.1.LiesOver w'.1] [w.1.LiesOver v.1] (y : v.Completion) :
    algebraMap w'.Completion w.Completion (algebraMap v.Completion w'.Completion y) =
      algebraMap v.Completion w.Completion y := by
  have hd : DenseRange (algebraMap K v.Completion) := denseRange_algebraMap_completion v
  have h1 : Continuous fun y : v.Completion => algebraMap w'.Completion w.Completion (algebraMap v.Completion w'.Completion y) :=
    (continuous_algebraMap_completion w' w).comp (continuous_algebraMap_completion v w')
  have h2 : Continuous fun y : v.Completion => algebraMap v.Completion w.Completion y :=
    continuous_algebraMap_completion v w
  have key := hd.equalizer h1 h2 (funext fun x => ?_)
  · exact congrFun key y

  show algebraMap w'.Completion w.Completion (algebraMap v.Completion w'.Completion (algebraMap K v.Completion x)) =
    algebraMap v.Completion w.Completion (algebraMap K v.Completion x)
  have e0 : algebraMap K v.Completion x = (((WithAbs.equiv v.1).symm x : WithAbs v.1) : v.Completion) := rfl
  rw [e0, Completion.algebraMap_coe, Completion.algebraMap_coe, Completion.algebraMap_coe]
  congr 2
  exact (IsScalarTower.algebraMap_apply (WithAbs v.1) (WithAbs w'.1) (WithAbs w.1) _).symm

theorem conorm_apply_infinitePlace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : InfiniteAdeleRing K) (w : InfinitePlace L) (u : InfinitePlace K) (hu : w.comap (algebraMap K L) = u)
    [w.1.LiesOver u.1] :
    (genuineInfinitePlaceData (K := K) (L := L)).conorm x w = algebraMap u.Completion w.Completion (x u) := by
  subst hu
  show psiFactor (w.comap (algebraMap K L)) w ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
  rw [psiFactor_tmul, map_one, mul_one]

theorem archConorm_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] (x : InfiniteAdeleRing K) :
    (genuineInfinitePlaceData (K := K') (L := K'')).conorm ((genuineInfinitePlaceData (K := K) (L := K')).conorm x) =
      (genuineInfinitePlaceData (K := K) (L := K'')).conorm x := by
  funext w
  have hv : w.comap (algebraMap K K'') = (w.comap (algebraMap K' K'')).comap (algebraMap K K') := by
    rw [IsScalarTower.algebraMap_eq K K' K'', comap_comp]
  haveI i1 : w.1.LiesOver (w.comap (algebraMap K' K'')).1 := liesOver_of_comap_eq rfl
  haveI i2 : (w.comap (algebraMap K' K'')).1.LiesOver ((w.comap (algebraMap K' K'')).comap (algebraMap K K')).1 :=
    liesOver_of_comap_eq rfl
  haveI i3 : w.1.LiesOver ((w.comap (algebraMap K' K'')).comap (algebraMap K K')).1 := liesOver_of_comap_eq hv
  rw [conorm_apply_infinitePlace K' K'' _ w (w.comap (algebraMap K' K'')) rfl,
    conorm_apply_infinitePlace K K' x (w.comap (algebraMap K' K'')) ((w.comap (algebraMap K' K'')).comap (algebraMap K K')) rfl,
    conorm_apply_infinitePlace K K'' x w ((w.comap (algebraMap K' K'')).comap (algebraMap K K')) hv]
  exact algebraMap_completion_comp K K' K'' _ _ w (x _)

end F0bTower

open F0bTower in
theorem solution
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] :
    (genuineβ K' K'').comp (genuineβ K K') = genuineβ K K'' := by
  refine RingHom.ext fun x => Prod.ext ?_ ?_
  · show (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K') (L := K'')).conorm
        ((M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := K')).conorm x.1) =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := K'')).conorm x.1
    exact archConorm_comp_of_tower K K' K'' x.1
  · show finiteConorm (𝓞 K') K' K'' (𝓞 K'') (finiteConorm (𝓞 K) K K' (𝓞 K') x.2) = finiteConorm (𝓞 K) K K'' (𝓞 K'') x.2
    exact RingHom.congr_fun (finiteConorm_comp_of_tower K K' K'') x.2

end S_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
end P2MW
export P2MW.S_M4aHerbrand_Bridge_genuineBeta_comp_of_tower (solution)
