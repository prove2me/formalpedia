-- Prove2me | solution 1 for OAI.Kadison.AtomicFactor.Decomposition.two_isometries
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:10:31.22975+00:00
-- url     : https://prove2.me/submissions/8511943b-efcf-437f-b4f1-13045cf11313

import Mathlib
import Definitions.Def_OAIQ039C000
import Definitions.Def_OAIQ039C003

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

lemma support_projection (s : Finset D.I) : IsStarProjection (D.support s) := by
  classical
  constructor
  · change D.support s*D.support s=D.support s
    rw [support,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · calc
        _=(D.v i*(star (D.v i)*D.v i))*star (D.v i) := by noncomm_ring
        _=D.v i*star (D.v i) := by rw [D.initial,D.source]
    · intro j hj hne
      calc
        _=(D.v i*(star (D.v i)*D.v j))*star (D.v j) := by noncomm_ring
        _=0 := by rw [D.cross i j hne.symm,mul_zero,zero_mul]
  · change star (D.support s)=D.support s
    rw [support,star_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [star_mul,star_star]

lemma support_norm_le (s : Finset D.I) : ‖D.support s‖≤1 :=
  (D.support_projection s).norm_le _

lemma support_tendsto (x : H) : Tendsto (fun s : Finset D.I => D.support s x) atTop (𝓝 x) :=
  D.strong x

lemma eq_zero_of_coefficients_zero {a : H →L[ℂ] H}
    (ha : ∀ i j,star (D.v i)*a*D.v j=0) : a=0 := by
  have hleft (i : D.I) : star (D.v i)*a=0 := by
    ext x
    have he (s : Finset D.I) : (star (D.v i)*a) (D.support s x)=0 := by
      have ht : (star (D.v i)*a)*D.support s=0 := by
        rw [support,Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [←mul_assoc,ha i j,zero_mul]
      exact congrArg (fun T : H →L[ℂ] H => T x) ht
    exact tendsto_nhds_unique
      (((star (D.v i)*a).continuous.tendsto x).comp (D.support_tendsto x))
      (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))
  ext x
  have he (s : Finset D.I) : D.support s (a x)=0 := by
    have ht : D.support s*a=0 := by
      rw [support,Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      rw [mul_assoc,hleft i,mul_zero]
    exact congrArg (fun T : H →L[ℂ] H => T x) ht
  exact tendsto_nhds_unique (D.support_tendsto (a x))
    (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))

lemma eq_of_coefficients_eq {a b : H →L[ℂ] H}
    (h : ∀ i j,star (D.v i)*a*D.v j=star (D.v i)*b*D.v j) : a=b := by
  apply sub_eq_zero.mp
  apply D.eq_zero_of_coefficients_zero
  intro i j
  rw [mul_sub,sub_mul,h i j,sub_self]

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

lemma finiteShift_star_mul (f : D.I → D.I) (hf : Function.Injective f) (s : Finset D.I) :
    star (D.finiteShift f s)*D.finiteShift f s=D.support s := by
  classical
  rw [finiteShift,star_sum,Finset.sum_mul,support]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · simp only [star_mul,star_star]
    calc
      _=(D.v i*(star (D.v (f i))*D.v (f i)))*star (D.v i) := by noncomm_ring
      _=D.v i*star (D.v i) := by rw [D.initial,D.source]
  · intro j hj hne
    simp only [star_mul,star_star]
    calc
      _=(D.v i*(star (D.v (f i))*D.v (f j)))*star (D.v j) := by noncomm_ring
      _=0 := by rw [D.cross (f i) (f j) (fun h => hne (hf h).symm),mul_zero,zero_mul]

lemma finiteShift_norm_le (f : D.I → D.I) (hf : Function.Injective f) (s : Finset D.I) :
    ‖D.finiteShift f s‖≤1 := by
  have he := D.support_norm_le s
  rw [←D.finiteShift_star_mul f hf s,CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg (D.finiteShift f s)]

lemma finiteShift_mul_val (f : D.I → D.I) (s : Finset D.I) {i : D.I} (hi : i∈s) :
    D.finiteShift f s*D.v i=D.v (f i) := by
  classical
  rw [finiteShift,Finset.sum_mul,Finset.sum_eq_single_of_mem i hi,mul_assoc,D.initial,D.source]
  intro j hj hne
  rw [mul_assoc,D.cross j i hne,mul_zero]

theorem exists_shift (f : D.I → D.I) (hf : Function.Injective f) :
    ∃ W : H →L[ℂ] H,W∈M ∧ ∀ i,W*D.v i=D.v (f i) := by
  classical
  let ω : Ultrafilter (Finset D.I) := Ultrafilter.of atTop
  have hω : (ω : Filter (Finset D.I))≤atTop := Ultrafilter.of_le _
  obtain ⟨W,hW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (D.finiteShift f) 1
    (by norm_num) (D.finiteShift_norm_le f hf)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Eventually.of_forall fun s => M.sum_mem (fun i _ => M.mul_mem (D.mem (f i)) (M.star_mem' (D.mem i))))
  refine ⟨W,hWM,?_⟩
  intro i
  ext x
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique (hlim (D.v i x) y)
  apply tendsto_const_nhds.congr'
  filter_upwards [hω (eventually_ge_atTop ({i}:Finset D.I))] with s hs
  have he := D.finiteShift_mul_val f s (i:=i) (hs (Finset.mem_singleton_self i))
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) he.symm

lemma shift_isometry (f : D.I → D.I) (hf : Function.Injective f)
    {W : H →L[ℂ] H} (hW : ∀ i,W*D.v i=D.v (f i)) : star W*W=1 := by
  apply D.eq_of_coefficients_eq
  intro i j
  calc
    star (D.v i)*(star W*W)*D.v j=star (W*D.v i)*(W*D.v j) := by
      rw [star_mul]; noncomm_ring
    _=star (D.v (f i))*D.v (f j) := by rw [hW i,hW j]
    _=star (D.v i)*D.v j := by
      by_cases hij : i=j
      · subst j; rw [D.initial,D.initial]
      · rw [D.cross i j hij,D.cross (f i) (f j) (fun h => hij (hf h))]
    _=star (D.v i)*1*D.v j := by rw [mul_one]

lemma shifts_orthogonal (f g : D.I → D.I) (hfg : ∀ i j,f i≠g j)
    {W V : H →L[ℂ] H} (hW : ∀ i,W*D.v i=D.v (f i))
    (hV : ∀ i,V*D.v i=D.v (g i)) : star W*V=0 := by
  apply D.eq_zero_of_coefficients_zero
  intro i j
  calc
    _=star (W*D.v i)*(V*D.v j) := by rw [star_mul]; noncomm_ring
    _=star (D.v (f i))*D.v (g j) := by rw [hW i,hV j]
    _=0 := D.cross _ _ (hfg i j)

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicInfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

theorem two_isometries_oai [Infinite D.I] :
    ∃ s t : M,star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  obtain ⟨e⟩ : Nonempty (D.I ≃ D.I×Bool) := by
    apply Cardinal.eq.mp
    rw [Cardinal.mk_prod,Cardinal.mk_bool]
    simpa using (Cardinal.mul_eq_left (Cardinal.aleph0_le_mk D.I)
      ((Cardinal.natCast_le_aleph0 (n:=2)).trans (Cardinal.aleph0_le_mk D.I)) (by norm_num)).symm
  let f : D.I → D.I := fun i => e.symm (i,false)
  let g : D.I → D.I := fun i => e.symm (i,true)
  have hf : Function.Injective f := by
    intro i j h
    exact congrArg Prod.fst (e.symm.injective h)
  have hg : Function.Injective g := by
    intro i j h
    exact congrArg Prod.fst (e.symm.injective h)
  have hfg : ∀ i j,f i≠g j := by
    intro i j h
    have he := congrArg Prod.snd (e.symm.injective h)
    exact Bool.false_ne_true he
  obtain ⟨W,hWM,hW⟩ := D.exists_shift f hf
  obtain ⟨V,hVM,hV⟩ := D.exists_shift g hg
  refine ⟨⟨W,hWM⟩,⟨V,hVM⟩,?_,?_,?_⟩
  · apply Subtype.ext
    exact D.shift_isometry f hf hW
  · apply Subtype.ext
    exact D.shift_isometry g hg hV
  · apply Subtype.ext
    exact D.shifts_orthogonal f g hfg hW hV

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.AtomicFactor.Decomposition.two_isometries_oai.{u_1} := @OAI.Kadison.AtomicFactor.Decomposition.two_isometries_oai.{u_1}
