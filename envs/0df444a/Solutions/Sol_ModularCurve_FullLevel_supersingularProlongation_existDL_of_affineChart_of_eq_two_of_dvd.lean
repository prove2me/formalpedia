-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_existDL_of_affineChart_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/21357a68-31ed-55e9-8442-fb9aa40ccb5d

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_two
import Theorems.Thm_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_existDL_of_affineChart_of_eq_two_of_dvd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace ExistDLReduce

theorem glue_resSurj (A : ValuationSubring (AlgebraicClosure ℚ)) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (A' : ValuationSubring ↥K')
    (hA' : ∀ x : ↥K', x ∈ A' ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    Function.Surjective (fun a : ↥A' => IsLocalRing.residue ↥A ⟨((a : ↥K') : AlgebraicClosure ℚ), (hA' a).mp a.2⟩) := by
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hcA, hsub, hm⟩ := hκ a a.2
  refine ⟨⟨⟨(c : AlgebraicClosure ℚ), K'.algebraMap_mem c⟩, (hA' _).mpr hcA⟩, ?_⟩
  change IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ = IsLocalRing.residue ↥A a
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hm

end ExistDLReduce

open ExistDLReduce in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) →
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ W₀ h1 h2a h2b h2c B alg hM1 hM2a hM2c hM3 hM5b FSS _ _ R hRW inst hdom ζ
  obtain ⟨Cs, ρ, hCs, hker, hρC, hρfrac, hρrange, hρE1⟩ := hM3 inst hdom ζ
  have hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers := fun f hf => by
    obtain ⟨hf0, hw⟩ := hM2a f hf
    exact (hRW ⟨f, hf0⟩).mpr hw
  obtain ⟨hfracR, hkerR⟩ := ModularCurve.FullLevel.supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_two q hq2 M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ
    Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0 F₀ W₀ h1 h2a h2b h2c B alg hM1 hM2a hM2c FSS R hRW hBR

  let red : ↥B →+* FSS := R.residue.comp (B.subtype.codRestrict R.integers (fun b => hBR _ b.2))
  have hred : ∀ b : ↥B, red b = R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ b.2⟩ := fun b => rfl
  have hfracR' : ∀ x : FSS, ∃ g h : ↥B, red h ≠ 0 ∧ x * red h = red g := hfracR
  have hkerEq : RingHom.ker red = RingHom.ker ρ := by
    ext b
    rw [RingHom.mem_ker, hred, hkerR, hker, Ideal.mem_span_singleton]
  have hκb := glue_resSurj A k₀ hκ Kb Ab hAb
  have hc1 : ∀ a : ↥Ab, red (@algebraMap ↥Ab ↥B _ _ alg a) =
      algebraMap (ResidueField ↥A) FSS (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) := by
    intro a
    rw [hred]
    have hmem : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ((hAb a).mp a.2)
    have : (⟨((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')), hBR _ (@algebraMap ↥Ab ↥B _ _ alg a).2⟩ : ↥R.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)), hmem⟩ := Subtype.ext (hM1 a)
    rw [this]
    exact R.residue_algebraMap ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩
  obtain ⟨e, he⟩ := RingHom.exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq red ρ hkerEq hfracR' hρfrac
    (@algebraMap ↥Ab ↥B _ _ alg) (fun a : ↥Ab => IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) hκb hc1 hρC
  refine ⟨Cs, e, hCs, ?_⟩
  intro γ hγ hτ hmem x

  have hγ' : γ⁻¹ ∈ Gamma0 M' := inv_mem hγ
  have key : ∀ b : ↥B, ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red b)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
      DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (red b) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by
    intro b
    have hb' : levelAutBar q M' ζ γ⁻¹ ((b : ↥B) : ↥(fieldBar q M')) ∈ B := hM5b ζ γ⁻¹ hγ' _ b.2
    have h1 : R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red b) = red ⟨_, hb'⟩ := by
      rw [hred, hred, AlgebraicCurve.RegularProlongation.resAut_residue]
    rw [h1, he, he]
    exact hρE1 γ hγ hmem b hb'

  obtain ⟨g, h, hh0, hx⟩ := hfracR' x
  have cm : ∀ y z : FSS, ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (y * z)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) = ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (y)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) * ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (z)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by
    intro y z; rw [map_mul, map_mul]; rfl
  have cm2 : ∀ y z : FSS, DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (y * z) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) = DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (y) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) * DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (z) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by
    intro y z; rw [map_mul, ← map_mul (DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩)]; rfl
  have hne : ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red h)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≠ 0 := by
    rw [key h, map_ne_zero_iff _ (DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩).injective, ne_eq, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ e.injective]
    exact hh0
  apply mul_right_cancel₀ hne
  calc ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (x)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) * ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red h)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))
      = ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (x * red h)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := (cm x (red h)).symm
    _ = ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red g)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by rw [hx]
    _ = DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (red g) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := key g
    _ = DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (x * red h) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by rw [hx]
    _ = DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) * DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (red h) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := cm2 x (red h)
    _ = DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e (x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) * ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ (red h)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by rw [key h]

end S_ModularCurve_FullLevel_supersingularProlongation_existDL_of_affineChart_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_existDL_of_affineChart_of_eq_two_of_dvd (solution)
