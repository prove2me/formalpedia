-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a99c868f-0f63-5ebe-ac55-9427a92d6611

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_LocalGL2_exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_mul_eq_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace W3G

open FLT.SmoothAdmissibleSchurCommutant Topology

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem exists_ball_subset_of_mem_nhds_zero {s : Set (v.adicCompletion ℚ)} (hs : s ∈ 𝓝 (0 : v.adicCompletion ℚ)) :
    ∃ k : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h =>
    γ.ne_zero ((map_eq_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).1 h)
  refine ⟨WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1, fun y hy => hγ ?_⟩
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding]
  calc Valued.v y ≤ WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) - 1) := hy
    _ < WithZero.exp (WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) :=
        WithZero.exp_lt_exp.2 (by omega)
    _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := WithZero.exp_log hne

theorem continuous_unipotentGL2 :
    Continuous fun t : v.adicCompletion ℚ => (AutomorphicForm.unipotentGL2 t : GL (Fin 2) (v.adicCompletion ℚ)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [AutomorphicForm.unipotentGL2, Units.inv_mk] <;> fun_prop

theorem unipotentGL2_eq (x : v.adicCompletion ℚ) :
    (AutomorphicForm.unipotentGL2 x : GL (Fin 2) (v.adicCompletion ℚ)) = upperUnipotent2 v x :=
  Units.ext rfl

variable (θ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

theorem principalSeries2Rep_apply_coe (g h : GL (Fin 2) (v.adicCompletion ℚ)) (f : ↥(principalSeries2 v θ)) :
    ((principalSeries2Rep θ g f : ↥(principalSeries2 v θ)) : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) h = (f : _ → ℂ) (h * g) :=
  rfl

variable (V : Submodule ℂ ↥(principalSeries2 v θ))

def subRep (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V) :
    GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ ↥V where
  toFun g := (principalSeries2Rep θ g).restrict fun w hw => hV g w hw
  map_one' := by
    ext w
    simp [LinearMap.restrict_apply]
  map_mul' g g' := by
    ext w
    simp [LinearMap.restrict_apply]

theorem subRep_apply (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) (w : ↥V) :
    subRep θ V hV g w = ⟨principalSeries2Rep θ g (w : ↥(principalSeries2 v θ)), hV g _ w.2⟩ :=
  rfl

theorem isSmoothRep_subRep (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V) :
    IsSmoothRep (V := ↥V) (subRep θ V hV) := by
  intro w
  obtain ⟨U, hUo, hU⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 v θ
      ((w : ↥(principalSeries2 v θ)) : _ → ℂ) (w : ↥(principalSeries2 v θ)).2
  refine Subgroup.isOpen_mono (H₁ := U) ?_ hUo
  intro k hk
  rw [mem_repStabilizer, subRep_apply]
  apply Subtype.ext
  apply Subtype.ext
  funext h
  show ((principalSeries2Rep θ k (w : ↥(principalSeries2 v θ)) : ↥(principalSeries2 v θ)) : _ → ℂ) h = _
  rw [principalSeries2Rep_apply_coe]
  exact hU k hk h

set_option maxHeartbeats 4000000 in
theorem main (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V)
    (hdeg : ∀ (ψ' : AddChar (v.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (ℓ : ↥V →ₗ[ℂ] ℂ),
        (∀ (x : v.adicCompletion ℚ) (w : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 v x) w, hV _ w w.2⟩ = ψ' x * ℓ w) → ℓ = 0)
    (x : v.adicCompletion ℚ) (f : ↥(principalSeries2 v θ)) (hf : f ∈ V) :
    principalSeries2Rep θ (upperUnipotent2 v x) f = f := by
  by_contra hx
  have hmove : subRep θ V hV (AutomorphicForm.unipotentGL2 x) ⟨f, hf⟩ ≠ ⟨f, hf⟩ := by
    intro h
    apply hx
    have := congrArg Subtype.val h
    rw [subRep_apply, unipotentGL2_eq] at this
    exact this
  obtain ⟨ψ, hψ1, Λ, hΛ0, hΛ⟩ :=
    LocalGL2.exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne ℚ v (V := ↥V)
      (subRep θ V hV) (isSmoothRep_subRep θ V hV) x ⟨f, hf⟩ hmove

  have hψk : ∃ k : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ y = 1 := by
    have hq : ∃ q, Λ q ≠ 0 := by
      by_contra h
      push Not at h
      exact hΛ0 (LinearMap.ext fun q => by rw [h q, LinearMap.zero_apply])
    obtain ⟨q, hq⟩ := hq
    have hop : IsOpen ((repStabilizer (V := ↥V) (subRep θ V hV) q : Subgroup _) : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
      isSmoothRep_subRep θ V hV q
    have hpre : {t : v.adicCompletion ℚ | AutomorphicForm.unipotentGL2 t ∈ repStabilizer (V := ↥V) (subRep θ V hV) q} ∈
        𝓝 (0 : v.adicCompletion ℚ) := by
      apply (hop.preimage continuous_unipotentGL2).mem_nhds
      show AutomorphicForm.unipotentGL2 (0 : v.adicCompletion ℚ) ∈ repStabilizer (V := ↥V) (subRep θ V hV) q
      rw [AutomorphicForm.unipotentGL2_zero]
      exact (repStabilizer (V := ↥V) (subRep θ V hV) q).one_mem
    obtain ⟨k, hk⟩ := exists_ball_subset_of_mem_nhds_zero hpre
    refine ⟨k, fun y hy => ?_⟩
    have hfix : subRep θ V hV (AutomorphicForm.unipotentGL2 y) q = q :=
      (mem_repStabilizer (V := ↥V) (subRep θ V hV)).1 (hk y hy)
    have := hΛ y q
    rw [hfix] at this
    exact (mul_eq_right₀ hq).1 this.symm
  have hΛ' : ∀ (x : v.adicCompletion ℚ) (w : ↥V),
      Λ ⟨principalSeries2Rep θ (upperUnipotent2 v x) w, hV _ w w.2⟩ = ψ x * Λ w := by
    intro x' w
    have := hΛ x' w
    rw [subRep_apply, unipotentGL2_eq] at this
    exact this
  exact hΛ0 (hdeg ψ hψk hψ1 Λ hΛ')

end W3G

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hdeg : ∀ (ψ' : AddChar (p.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (ℓ : ↥V →ₗ[ℂ] ℂ),
        (∀ (x : p.adicCompletion ℚ) (v : ↥V),
          ℓ ⟨principalSeries2Rep θ (upperUnipotent2 p x) v, hV _ v v.2⟩ = ψ' x * ℓ v) → ℓ = 0)
    (x : p.adicCompletion ℚ) (v : ↥(principalSeries2 p θ)) (hv : v ∈ V) :
    principalSeries2Rep θ (upperUnipotent2 p x) v = v :=
  W3G.main θ V hV hdeg x v hv

end S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_eq_self_of_forall_whittaker_functional_eq_zero (solution)
