-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7cee9f07-1a83-58a2-9df0-0b8411d44f5d

import Theorems.Thm_AlgebraicCurve_red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one
import Theorems.Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem RedNat.ofAlgAut_smul_place {K F : Type} [Field K] [Field F] [Algebra K F]
    (σ : F ≃ₐ[K] F) (P : AlgebraicCurve.Place K F) :
    AlgebraicCurve.SemilinearAut.ofAlgAut σ • P = σ • P := by
  ext1
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv]
  rfl

set_option maxHeartbeats 16000000 in
theorem RedNat.stab_level
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (ζ : ModularCurve.FullLevel.Idx q)
    (w : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) (hw : w ∈ (⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1))) :
    ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut.ofAlgAut (ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹)) w ∈
      (⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1)) := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
  intro s hs
  obtain ⟨τ, hτ, hτπ, rfl⟩ := hs
  have hcomm := ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one
    q M' hqM' P hP π hπ hτ hτπ ζ γ⁻¹ (inv_mem hγ)
  rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hw _ ⟨τ, hτ, hτπ, rfl⟩]

set_option maxHeartbeats 16000000 in
theorem RedNat.stab_inert
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (w : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) (hw : w ∈ (⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1))) :
    ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) w ∈
      (⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1)) := by
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
  intro s hs
  obtain ⟨τ₁, hτ₁, hτ₁π, rfl⟩ := hs
  have hτD : τ ∈ P.decompositionSubgroup ℚ := by
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hτ
    exact d.2
  obtain ⟨hconj, hconjπ⟩ :=
    (ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
      q P hP π hπ).2.1 τ⁻¹ (inv_mem hτD) τ₁ hτ₁ hτ₁π
  have key : τ₁ * τ = τ * (τ⁻¹ * τ₁ * τ⁻¹⁻¹) := by group
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, key, map_mul, map_mul, Module.End.mul_apply,
    hw _ ⟨_, hconj, hconjπ, rfl⟩]

set_option maxHeartbeats 16000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField P)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ModularCurve.ssPlaces q M' (IsLocalRing.ResidueField P))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField P))]
    (hle : ModularCurve.modularFunctionFieldBar M' ≤ ModularCurve.FullLevel.fieldBar q M')
    (R₀ : AlgebraicCurve.ConstantReduction P ↥(ModularCurve.modularFunctionFieldBar M')
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M'))

    (hR₀ : ∀ (y : LaurentSeries ↥P) (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.modularFunctionFieldBar M'),
      ∃ h : (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ↥(ModularCurve.modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField P) M') :
            LaurentSeries (IsLocalRing.ResidueField P)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥P) y) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    let S : Set (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) :=
      {s | ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
        s = ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ}
    let Vinv : Submodule ℚ_[lam] (ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) := ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1)
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →

      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ ℓ : CuspidalType.ProjLine q, ∃ ℓ' : CuspidalType.ProjLine q,
        ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), Q ∈ (𝒞.CIg ℓ).dom →
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ • Q ∈
            (𝒞.CIg ℓ').dom) →
      ∀ (red : ↥Vinv →ₗ[ℚ_[lam]]
      ∀ i, ModularCurve.RationalTateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i))),
      (∀ (v : ↥Vinv)
      (x : TateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))), (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x →
      ∀ (k : ℕ) (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (hD : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.FullLevel.fieldBar q M'))),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) k x →
      ∀ Di : Fin 𝒞.teleN → Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'), D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (𝒞.teleChart i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i)),
          red v i = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField P) (F := 𝒞.teleFbar i),
            (E : Divisor (IsLocalRing.ResidueField P) (𝒞.teleFbar i)) =
                Finsupp.mapDomain (𝒞.teleChart i).placeMap (Di i) →
              TateModule.proj lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar i)) k y = Pic0.mk E) →
      (∀ v : ↥Vinv,
      (red v = 0 ↔ (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∈ Submodule.span ℚ_[lam] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s w - w})) →
      (∀ (v : ↥Vinv)
      (x : TateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))), (v : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) = (1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x →
      ∀ k : ℕ, ∃ (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (hD : D ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.FullLevel.fieldBar q M'))) (Di : Fin 𝒞.teleN → Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')),
        Pic0.mk ⟨D, hD⟩ = TateModule.proj lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) k x ∧
        D = ∑ i, Di i ∧ (∀ i, ∀ P ∈ (Di i).support, P ∈ (𝒞.teleChart i).dom) ∧ ∀ i, Divisor.degree (Di i) = 0) →
      (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, Q.IsRational) →
            ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ (s : ↥W),
        ∃ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
          ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s))
              (ModularCurve.arithmeticGalois
                (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) φ.toRingEquiv ∧
          ∀ (w : ↥Vinv) (hw : ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ) (w : ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∈ Vinv),
            red ⟨_, hw⟩ (𝒞.eSS s) = ModularCurve.rationalGaloisRep lam (Pic0 (IsLocalRing.ResidueField P) (𝒞.teleFbar (𝒞.eSS s)))
                (𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s)) φ (red w (𝒞.eSS s)) := by
  intro S Vinv 𝒞 h1 hDr hIgU h3 h4 h5 h6 h7 h8 h9 hIgDom red hred hker hrep hratF τ hτ s

  set g : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') := ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ with hg

  have ha := h9.1 τ hτ

  have key : ∃ φ : 𝒞.teleFbar (𝒞.eSS s) ≃ₐ[IsLocalRing.ResidueField P] 𝒞.teleFbar (𝒞.eSS s),
      ModularCurve.FullLevel.SemistableCovering.InducesOnChart (𝒞.teleChart (𝒞.eSS s)) g φ.toRingEquiv ∧
      (∀ Q, Q ∈ (𝒞.teleChart (𝒞.eSS s)).dom ↔ g • Q ∈ (𝒞.teleChart (𝒞.eSS s)).dom) ∧
      ∀ Q ∈ (𝒞.teleChart (𝒞.eSS s)).dom, (𝒞.teleChart (𝒞.eSS s)).placeMap (g • Q) =
        SemilinearAut.ofAlgAut φ • (𝒞.teleChart (𝒞.eSS s)).placeMap Q := by
    refine (𝒞.teleChart_eIdx_iff (fun j Cc => ∃ φ : 𝒞.sumFbar j ≃ₐ[IsLocalRing.ResidueField P] 𝒞.sumFbar j,
      ModularCurve.FullLevel.SemistableCovering.InducesOnChart Cc g φ.toRingEquiv ∧
      (∀ Q, Q ∈ Cc.dom ↔ g • Q ∈ Cc.dom) ∧
      ∀ Q ∈ Cc.dom, Cc.placeMap (g • Q) = SemilinearAut.ofAlgAut φ • Cc.placeMap Q) (Sum.inr s)).2 ?_
    obtain ⟨-, hdom₀, φ₀, hind₀, hpl₀⟩ := ha s
    exact ⟨φ₀, hind₀, hdom₀, hpl₀⟩
  obtain ⟨φ, ⟨hint, hres⟩, hdom, hplace⟩ := key

  have hperm : ∀ j : Fin 𝒞.teleN, ∃ j' : Fin 𝒞.teleN, ∀ Q : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'),
      Q ∈ (𝒞.teleChart j).dom → g • Q ∈ (𝒞.teleChart j').dom := by
    intro j
    rcases 𝒞.eIg_or_eSS j with ⟨ℓ, rfl⟩ | ⟨s', rfl⟩
    · obtain ⟨ℓ', hℓ'⟩ := hIgDom τ hτ ℓ
      refine ⟨𝒞.eIg ℓ', fun Q hQ => ?_⟩
      rw [𝒞.teleChart_eIg_dom] at hQ ⊢
      exact hℓ' Q hQ
    · refine ⟨𝒞.eSS s', fun Q hQ => ?_⟩
      rw [𝒞.teleChart_eSS_dom] at hQ ⊢
      exact ((ha s').2.1 Q).1 hQ
  refine ⟨φ, ⟨hint, hres⟩, fun w hw => ?_⟩
  exact AlgebraicCurve.red_rationalGaloisRep_apply_eq_rationalGaloisRep_red_of_inducesOnChart_of_placeMap_smul_of_isRational_of_mem_invariants
    P ↥(ModularCurve.FullLevel.fieldBar q M') 𝒞.teleN 𝒞.teleFbar 𝒞.teleChart 𝒞.isRational_teleFbar hratF lam Vinv red hred hrep g
    (fun v hv => RedNat.stab_inert q M' lam P hP π hπ τ hτ v hv) (𝒞.eSS s) φ hint hres hdom hplace hperm w

end S_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_algEquiv_inducesOnChart_arithmeticGalois_and_red_eq_of_semistableCovering_of_igusaDom_of_eq_two (solution)
