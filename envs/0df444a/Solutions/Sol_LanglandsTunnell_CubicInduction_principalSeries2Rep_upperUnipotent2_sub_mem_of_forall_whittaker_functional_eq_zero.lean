-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1e6df40f-74c2-5a32-9eed-01c2b9971fa6

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

namespace P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace W3qG

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

def quotRep (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V) :
    GL (Fin 2) (v.adicCompletion ℚ) →* Module.End ℂ (↥(principalSeries2 v θ) ⧸ V) where
  toFun g := V.mapQ V (principalSeries2Rep θ g) fun w hw => hV g w hw
  map_one' := by
    apply Submodule.linearMap_qext
    ext f
    simp [Submodule.mapQ_apply]
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext f
    simp [Submodule.mapQ_apply, map_mul]

theorem quotRep_mk (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) (f : ↥(principalSeries2 v θ)) :
    quotRep θ V hV g (Submodule.Quotient.mk f) = Submodule.Quotient.mk (principalSeries2Rep θ g f) :=
  rfl

theorem isSmoothRep_quotRep (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V) :
    IsSmoothRep (quotRep θ V hV) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective V q
  obtain ⟨U, hUo, hU⟩ :=
    LanglandsTunnell.CubicInduction.exists_isOpen_forall_mul_eq_of_mem_principalSeries2 v θ (f : _ → ℂ) f.2
  refine Subgroup.isOpen_mono (H₁ := U) ?_ hUo
  intro k hk
  rw [mem_repStabilizer, quotRep_mk]
  congr 1
  apply Subtype.ext
  funext h
  rw [principalSeries2Rep_apply_coe]
  exact hU k hk h

theorem main (hV : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)), ∀ w ∈ V, principalSeries2Rep θ g w ∈ V)
    (hdeg : ∀ (ψ' : AddChar (v.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (L : ↥(principalSeries2 v θ) →ₗ[ℂ] ℂ),
        (∀ (x : v.adicCompletion ℚ) (f : ↥(principalSeries2 v θ)),
          L (principalSeries2Rep θ (upperUnipotent2 v x) f) = ψ' x * L f) → (∀ w ∈ V, L w = 0) → L = 0)
    (x : v.adicCompletion ℚ) (f : ↥(principalSeries2 v θ)) :
    principalSeries2Rep θ (upperUnipotent2 v x) f - f ∈ V := by
  by_contra hx

  have hmove : quotRep θ V hV (AutomorphicForm.unipotentGL2 x) (Submodule.Quotient.mk f) ≠ Submodule.Quotient.mk f := by
    rw [quotRep_mk, unipotentGL2_eq, Ne, Submodule.Quotient.eq]
    exact hx
  obtain ⟨ψ, hψ1, Λ, hΛ0, hΛ⟩ :=
    LocalGL2.exists_whittakerFunctional_ne_zero_of_isSmoothRep_of_unipotentGL2_apply_ne ℚ v
      (quotRep θ V hV) (isSmoothRep_quotRep θ V hV) x (Submodule.Quotient.mk f) hmove

  have hψk : ∃ k : ℤ, ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ y = 1 := by
    have hq : ∃ q, Λ q ≠ 0 := by
      by_contra h
      push Not at h
      exact hΛ0 (LinearMap.ext fun q => by rw [h q, LinearMap.zero_apply])
    obtain ⟨q, hq⟩ := hq
    have hop : IsOpen ((repStabilizer (quotRep θ V hV) q : Subgroup _) : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
      isSmoothRep_quotRep θ V hV q
    have hpre : {t : v.adicCompletion ℚ | AutomorphicForm.unipotentGL2 t ∈ repStabilizer (quotRep θ V hV) q} ∈
        𝓝 (0 : v.adicCompletion ℚ) := by
      apply (hop.preimage continuous_unipotentGL2).mem_nhds
      show AutomorphicForm.unipotentGL2 (0 : v.adicCompletion ℚ) ∈ repStabilizer (quotRep θ V hV) q
      rw [AutomorphicForm.unipotentGL2_zero]
      exact (repStabilizer (quotRep θ V hV) q).one_mem
    obtain ⟨k, hk⟩ := exists_ball_subset_of_mem_nhds_zero hpre
    refine ⟨k, fun y hy => ?_⟩
    have hfix : quotRep θ V hV (AutomorphicForm.unipotentGL2 y) q = q := (mem_repStabilizer _).1 (hk y hy)
    have := hΛ y q
    rw [hfix] at this
    exact (mul_eq_right₀ hq).1 this.symm

  set L : ↥(principalSeries2 v θ) →ₗ[ℂ] ℂ := Λ.comp V.mkQ with hL
  have hLeq : ∀ (x : v.adicCompletion ℚ) (f : ↥(principalSeries2 v θ)),
      L (principalSeries2Rep θ (upperUnipotent2 v x) f) = ψ x * L f := by
    intro x' f'
    simp only [hL, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← quotRep_mk θ V hV, ← unipotentGL2_eq]
    exact hΛ x' _
  have hLV : ∀ w ∈ V, L w = 0 := by
    intro w hw
    simp only [hL, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero V).2 hw, map_zero]
  have hL0 := hdeg ψ hψk hψ1 L hLeq hLV
  apply hΛ0
  apply Submodule.linearMap_qext
  rw [← hL, hL0, LinearMap.zero_comp]

end W3qG

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (V : Submodule ℂ ↥(principalSeries2 p θ))
    (hV : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)), ∀ v ∈ V, principalSeries2Rep θ g v ∈ V)
    (hdeg : ∀ (ψ' : AddChar (p.adicCompletion ℚ) ℂ),
      (∃ k : ℤ, ∀ y : p.adicCompletion ℚ, Valued.v y ≤ WithZero.exp k → ψ' y = 1) → ψ' ≠ 1 →
      ∀ (L : ↥(principalSeries2 p θ) →ₗ[ℂ] ℂ),
        (∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)),
          L (principalSeries2Rep θ (upperUnipotent2 p x) f) = ψ' x * L f) → (∀ v ∈ V, L v = 0) → L = 0)
    (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p θ)) :
    principalSeries2Rep θ (upperUnipotent2 p x) f - f ∈ V :=
  W3qG.main θ V hV hdeg x f

end S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_principalSeries2Rep_upperUnipotent2_sub_mem_of_forall_whittaker_functional_eq_zero (solution)
