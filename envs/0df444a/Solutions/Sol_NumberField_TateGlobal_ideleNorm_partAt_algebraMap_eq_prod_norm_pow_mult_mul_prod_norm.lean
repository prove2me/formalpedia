-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3874c8c9-bdb0-5430-8f14-b549d3261e8f

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

namespace NSAux44

open scoped Classical in
theorem snd_partAt_empty (K : Type) [Field K] [NumberField K] (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((NumberField.Idele.partAt K ∅ x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := by
  refine Subtype.ext (funext fun v => ?_)
  show (if v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))) then ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
    else 1) = (1 : FiniteAdeleRing (𝓞 K) K) v
  rw [if_neg (Finset.notMem_empty v)]
  rfl

open scoped Classical in
theorem fst_partAt (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (AdeleRing (𝓞 K) K)ˣ) :
    ((NumberField.Idele.partAt K S x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = (x : AdeleRing (𝓞 K) K).1 := rfl

theorem snd_algebraMap_apply (K : Type) [Field K] [NumberField K] (k : K) (v : HeightOneSpectrum (𝓞 K)) :
    ((algebraMap K (AdeleRing (𝓞 K) K) k).2 : FiniteAdeleRing (𝓞 K) K) v = algebraMap K (v.adicCompletion K) k := rfl

end NSAux44

open NSAux44 in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ) :
    NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) =
      (∏ w : InfinitePlace K, ‖(algebraMap K (AdeleRing (𝓞 K) K) (a : K)).1 w‖ ^ w.mult) *
        ∏ v ∈ S, ‖((algebraMap K (AdeleRing (𝓞 K) K) (a : K)).2 : FiniteAdeleRing (𝓞 K) K) v‖ := by
  have h1 := NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one K S ∅
    (Finset.disjoint_empty_left S) a
  have h2 := NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one K ∅ S
    (Finset.disjoint_empty_right S) a
  simp only [Finset.prod_empty, mul_one, Finset.union_empty, Finset.empty_union] at h1 h2
  have hP0 : (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (if v ∈ S then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a : K)‖)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have hNS := mul_right_cancel₀ hP0 (h1.trans h2.symm)
  rw [hNS, NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (snd_partAt_empty K _),
    fst_partAt]
  simp only [snd_algebraMap_apply]
  rfl

end S_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_algebraMap_eq_prod_norm_pow_mult_mul_prod_norm (solution)
