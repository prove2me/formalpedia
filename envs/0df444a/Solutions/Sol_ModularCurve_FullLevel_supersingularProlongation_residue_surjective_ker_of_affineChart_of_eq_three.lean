-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e3e403cc-0d99-5987-b5b1-2931bc2c9c9c

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ValuationSubring_eq_of_constantsTower_of_forall_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace B2SubV

abbrev FB (q M' : ℕ) : Type := ↥(fieldBar q M')

variable (q M' : ℕ) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

scoped instance algK : Algebra ↥k₀ (FB q M') :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

def ιL : AlgebraicClosure ℚ →ₐ[↥k₀] FB q M' :=
  { algebraMap (AlgebraicClosure ℚ) (FB q M') with commutes' := fun _ => rfl }

@[scoped simp] theorem ιL_apply (x : AlgebraicClosure ℚ) : ιL q M' k₀ x = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def Lbar : IntermediateField ↥k₀ (FB q M') := (ιL q M' k₀).fieldRange

def eL : AlgebraicClosure ℚ ≃ₐ[↥k₀] ↥(Lbar q M' k₀) := AlgEquiv.ofInjectiveField (ιL q M' k₀)

theorem eL_apply (x : AlgebraicClosure ℚ) :
    ((eL q M' k₀ x : ↥(Lbar q M' k₀)) : FB q M') = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def AL (A : ValuationSubring (AlgebraicClosure ℚ)) : ValuationSubring ↥(Lbar q M' k₀) :=
  A.comap (eL q M' k₀).symm.toAlgHom.toRingHom

theorem mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : ↥(Lbar q M' k₀)) :
    x ∈ AL q M' k₀ A ↔ (eL q M' k₀).symm x ∈ A := Iff.rfl

theorem eL_mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    eL q M' k₀ x ∈ AL q M' k₀ A ↔ x ∈ A := by
  rw [mem_AL, AlgEquiv.symm_apply_apply]

end B2SubV
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three.B2SubV"

open B2SubV in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (hhensb : HenselianLocalRing ↥Ab)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) → (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) → IsDiscreteValuationRing ↥W₀ →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) →
      ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) →
        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        ∀ (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers),
        (∀ x : FSS, ∃ g h : ↥B, R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ≠ 0 ∧ x * R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ = R.residue ⟨((g : ↥B) : ↥(fieldBar q M')), hBR _ (g).2⟩) ∧
        (∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ = 0 ↔ @algebraMap ↥Ab ↥B _ _ alg ϖb ∣ b) := by
  intro F₀ W₀ hK1 hK2a hK2b hK2c B alg halgB hBW hM2c FSS _ _ R hRW hBR
  classical
  obtain ⟨hπW, hunifW⟩ := hK2c

  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI halg : Algebra.IsAlgebraic ↥k₀ ↥(Lbar q M' k₀) := by
    haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
    exact (eL q M' k₀).isAlgebraic
  have hkL : ∀ c : ↥k₀, algebraMap ↥k₀ ↥(Lbar q M' k₀) c = eL q M' k₀ (c : AlgebraicClosure ℚ) := fun c =>
    ((eL q M' k₀).commutes c).symm
  have hcomapEq : A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) = (AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)) := by
    ext x
    show (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥(Lbar q M' k₀) x ∈ AL q M' k₀ A
    rw [hkL, eL_mem_AL]
  obtain ⟨hπ', hunif'⟩ : ∃ hπ' : π₀ ∈ (AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)),
      maximalIdeal ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) = Ideal.span {⟨π₀, hπ'⟩} :=
    hcomapEq ▸ (⟨hπ, hunif⟩ : ∃ hπ' : π₀ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)),
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {⟨π₀, hπ'⟩})
  have hdvr' : IsDiscreteValuationRing ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) := hcomapEq ▸ hdvr
  have hhens' : HenselianLocalRing ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) := hcomapEq ▸ hhens
  have hres' : IsAlgClosed (ResidueField ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)))) := hcomapEq ▸ hres
  obtain ⟨hint, htower⟩ :=
    @ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian ↥k₀ (FB q M') _ _ _ _ (Lbar q M' k₀)
      halg (AL q M' k₀ A) π₀ hπ' hdvr' hunif' hhens' hres'

  have hgen : Lbar q M' k₀ ⊔ F₀ = ⊤ := by
    have : Lbar q M' k₀ = IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).mp hx
        exact IntermediateField.subset_adjoin ↥k₀ _ ⟨y, rfl⟩
      · exact IntermediateField.adjoin_le_iff.mpr fun x ⟨y, hy⟩ => (AlgHom.mem_fieldRange).mpr ⟨y, hy⟩
    rw [this]; exact hK1
  have hagree : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(Lbar q M' k₀) x ∈ AL q M' k₀ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀ := by
    intro x; rw [hkL, eL_mem_AL]; exact hK2a x
  obtain ⟨O, hOA, hOF₀, hOres, hOsm⟩ :=
    ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral ↥k₀ (FB q M') (Lbar q M' k₀) F₀ hgen
      (AL q M' k₀ A) W₀ hagree hK2b π₀ hπW hunifW hint htower
  have hOR : O = R.integers :=
    ValuationSubring.eq_of_constantsTower_of_forall_mem_iff ↥k₀ (FB q M') (Lbar q M' k₀) F₀ hgen
      (AL q M' k₀ A) W₀ hagree hK2b π₀ hπW hunifW hint htower O R.integers hOF₀ hRW
  subst hOR

  have hϖbA : (((ϖb : ↥Kb) : AlgebraicClosure ℚ)) ∈ A := (hAb _).mp ϖb.2
  have hϖbres : IsLocalRing.residue ↥A ⟨_, hϖbA⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hmem : ϖb ∈ maximalIdeal ↥Ab := by rw [hϖb]; exact Ideal.mem_span_singleton_self ϖb
    apply (IsLocalRing.mem_maximalIdeal _).mp hmem

    have hinvA : (((ϖb : ↥Kb) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
      obtain ⟨v, hv⟩ := hu
      have h1 : ((v : ↥A) : AlgebraicClosure ℚ) * (((v⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = 1 := by
        rw [← MulMemClass.coe_mul, v.mul_inv]; rfl
      have h2 : ((v : ↥A) : AlgebraicClosure ℚ) = ((ϖb : ↥Kb) : AlgebraicClosure ℚ) := congrArg Subtype.val hv
      rw [h2] at h1
      rw [inv_eq_of_mul_eq_one_right h1]; exact ((v⁻¹ : (↥A)ˣ) : ↥A).2
    have hinvAb : ((ϖb : ↥Kb))⁻¹ ∈ Ab := by
      rw [hAb]; push_cast; exact hinvA
    have hne : ((ϖb : ↥Ab) : ↥Kb) ≠ 0 := fun h => hϖb0 (Subtype.ext h)
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvAb⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
  have hker : ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ b.2⟩ = 0 ↔ @algebraMap ↥Ab ↥B _ _ alg ϖb ∣ b := by
    intro b
    constructor
    · intro hb0
      by_contra hndvd
      have hb0' : (b : ↥(fieldBar q M')) ≠ 0 := by
        intro h
        apply hndvd
        have : b = 0 := Subtype.ext h
        rw [this]; exact dvd_zero _
      obtain ⟨hbF₀, hbW₀⟩ := hBW _ b.2

      have hinvF₀ : (b : ↥(fieldBar q M'))⁻¹ ∈ F₀ := inv_mem hbF₀
      have hinvW₀ : (⟨_, hinvF₀⟩ : ↥F₀) ∈ W₀ := by
        rw [hM2c]
        exact ⟨1, b, hndvd, by rw [inv_mul_cancel₀ hb0']; rfl⟩
      have hinvR : (b : ↥(fieldBar q M'))⁻¹ ∈ R.integers := (hRW ⟨_, hinvF₀⟩).mpr hinvW₀
      apply R.residue_ne_zero_of_isUnit _ hb0
      exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvR⟩, Subtype.ext (mul_inv_cancel₀ hb0')⟩
    · rintro ⟨c, hc⟩
      have : (⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ b.2⟩ : ↥R.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (((ϖb : ↥Kb) : AlgebraicClosure ℚ)),
            (R.algebraMap_mem_iff _).mpr hϖbA⟩ * ⟨((c : ↥B) : ↥(fieldBar q M')), hBR _ c.2⟩ := by
        apply Subtype.ext
        show ((b : ↥B) : ↥(fieldBar q M')) = _ * ((c : ↥B) : ↥(fieldBar q M'))
        rw [hc, Subring.coe_mul, halgB]
      rw [this, map_mul, R.residue_algebraMap ⟨_, hϖbA⟩, hϖbres, map_zero, zero_mul]
  refine ⟨?_, hker⟩

  intro x
  obtain ⟨w, rfl⟩ := R.residue_surjective x
  obtain ⟨f₀, hf₀R, hwf⟩ := hOres w
  have hresw : R.residue w = R.residue ⟨_, hf₀R⟩ := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, R.ker_residue]; exact hwf
  obtain ⟨g, h, hndvd, hgh⟩ := (hM2c (f₀ : ↥F₀)).mp f₀.2
  have hh0 : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ h.2⟩ ≠ 0 := fun h0 => hndvd ((hker h).mp h0)
  refine ⟨g, h, hh0, ?_⟩
  rw [hresw, ← map_mul]
  congr 1
  exact Subtype.ext hgh

end
end S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three (solution)
