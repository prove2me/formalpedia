-- Prove2me | solution 1 for NumberField.LevelArith.exists_kummerChar_eq_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f0b58bd3-d0e9-5fff-84fe-0678077c1526

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import Theorems.Thm_groupCohomology_Kummer_kummerHom_surjective
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_kummerChar_eq_of_continuous

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

local instance CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace CycBaseKummer

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

include hζ in

lemma pow_val_add (a b : ZMod p) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

include hζ in

lemma eq_of_pow_val_eq {a b : ZMod p} (h : ζ ^ a.val = ζ ^ b.val) : a = b :=
  ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

include hζ in
lemma eq_zero_of_pow_val_eq_one {a : ZMod p} (h : ζ ^ a.val = 1) : a = 0 :=
  eq_of_pow_val_eq p ζ hζ (by rw [h, ZMod.val_zero, pow_zero])

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ))

lemma apply_eq_of_mem {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ F.fixingSubgroup)
    {z : AlgebraicClosure ℚ} (hz : z ∈ F) : σ z = z :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ z hz

include hζ in

lemma mem_of_pow_eq_one (hζF : ζ ∈ F) {ε : AlgebraicClosure ℚ} (hε : ε ^ p = 1) : ε ∈ F := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hε
  exact pow_mem hζF i

lemma kummerChar_eq_zero_of_apply_eq (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup)
    (h : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = kummerRoot p F x) :
    kummerChar p ζ hζ F x σ = 0 := by
  apply eq_zero_of_pow_val_eq_one p ζ hζ
  have h2 := kummerChar_spec p ζ hζ F x σ
  rw [h] at h2

  have h3 := mul_left_eq_self₀.mp h2.symm
  exact h3.resolve_right (kummerRoot_ne_zero p F x)

end CycBaseKummer

namespace CycBaseKummerSurj

variable {p : ℕ} [Fact p.Prime]

lemma pow_val_add' {M : Type} [Monoid M] {u : M} (hu : u ^ p = 1) (a b : ZMod p) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hu, one_pow, one_mul]

lemma conj_mem_fixingSubgroup (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [hE : Normal ℚ E]
    {s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hs : s ∈ E.fixingSubgroup)
    (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : h⁻¹ * s * h ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hhx : h x ∈ E := (IntermediateField.normal_iff_forall_map_le'.1 hE h) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hhx]
  simp

theorem fixingSubgroup_normal (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ E] :
    E.fixingSubgroup.Normal :=
  ⟨fun s hs g => by simpa using conj_mem_fixingSubgroup E hs g⁻¹⟩

lemma levelGal_surjective (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [Normal ↥K ↥(levelField K L hKL)] : Function.Surjective (levelGal K L hKL) := by
  intro g
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL))
    (E := AlgebraicClosure ℚ) g
  refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, ?_⟩
  show (AlgEquiv.restrictNormalHom _) ((IntermediateField.fixingSubgroupEquiv K)
    ((IntermediateField.fixingSubgroupEquiv K).symm σ)) = g
  rw [MulEquiv.apply_symm_apply]; exact hσ

lemma mem_fixingSubgroup_of_levelGal_eq_one (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup) (h1 : levelGal K L hKL γ = 1) :
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  have h := levelGal_apply_coe K L hKL γ ⟨z, (IntermediateField.mem_extendScalars hKL).2 hz⟩
  rw [h1, AlgEquiv.one_apply] at h
  exact h.symm

omit [Fact p.Prime] in

lemma smul_rootsOfUnity_eq_self {K L : Type} [Field K] [Field L] [Algebra K L]
    (hμ : ∀ m : ↥(rootsOfUnity p L), ((m : Lˣ) : L) ∈ Set.range (algebraMap K L))
    (g : L ≃ₐ[K] L) (m : ↥(rootsOfUnity p L)) : g • m = m := by
  apply Subtype.ext
  rw [groupCohomology.Kummer.coe_smul_rootsOfUnity]
  exact groupCohomology.Kummer.smul_units_eq_self_of_mem_range g (hμ m)

omit [Fact p.Prime] in

lemma kummerCocycleRoots_eq_of_kummerClass_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    (htriv : ∀ (g : L ≃ₐ[K] L) (m : ↥(rootsOfUnity p L)), g • m = m)
    {a : Kˣ} {α : Lˣ} (hα : algebraMap K L (a : K) = (α : L) ^ p)
    {f : (L ≃ₐ[K] L) → ↥(rootsOfUnity p L)} (hf : groupCohomology.IsMulCocycle₁ f)
    (hcl : groupCohomology.Kummer.kummerClass hα = groupCohomology.H1π _ (groupCohomology.cocyclesOfIsMulCocycle₁ hf))
    (g : L ≃ₐ[K] L) : groupCohomology.Kummer.kummerCocycleRoots hα g = f g := by
  have h1 := (groupCohomology.H1π_eq_iff _ _).mp hcl
  rw [groupCohomology.coboundaries₁] at h1
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp h1
  have h2 := congrFun hm g
  rw [groupCohomology.d₀₁_hom_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, htriv] at h2
  change m - m = _ at h2
  rw [sub_self, Pi.sub_apply, eq_comm, sub_eq_zero] at h2
  have e2 := groupCohomology.cocyclesOfIsMulCocycle₁_coe hf g
  have e3 : (groupCohomology.Kummer.kummerCocycles hα) g =
      Additive.ofMul (groupCohomology.Kummer.kummerCocycleRoots hα g) := rfl
  rw [e3] at h2
  exact Additive.ofMul.injective (h2.trans e2)

lemma kummerChar_eq_of_apply_root (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F) (χ : ↥F.fixingSubgroup → ZMod p)
    (x : (↥F)ˣ) (α : AlgebraicClosure ℚ) (hαp : α ^ p = ((x : ↥F) : AlgebraicClosure ℚ))
    (hσα : ∀ σ : ↥F.fixingSubgroup, (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) α = ζ ^ (χ σ).val * α)
    (σ : ↥F.fixingSubgroup) : kummerChar p ζ hζ F x σ = χ σ := by
  have hp : p.Prime := Fact.out
  apply CycBaseKummer.eq_of_pow_val_eq p ζ hζ
  have hy0 := kummerRoot_ne_zero p F x
  have hα0 : α ≠ 0 := by
    intro h; apply hy0
    have : ((x : ↥F) : AlgebraicClosure ℚ) = 0 := by rw [← hαp, h, zero_pow hp.ne_zero]
    have h2 := kummerRoot_pow p F x
    rw [this] at h2
    exact pow_eq_zero_iff hp.ne_zero |>.mp h2
  have hε : (kummerRoot p F x / α) ^ p = 1 := by
    rw [div_pow, kummerRoot_pow, hαp, div_self]
    rw [← hαp]; exact pow_ne_zero _ hα0
  have hσε := CycBaseKummer.apply_eq_of_mem F σ.2 (CycBaseKummer.mem_of_pow_eq_one p ζ hζ F hζF hε)
  have hyeq : kummerRoot p F x = kummerRoot p F x / α * α := (div_mul_cancel₀ _ hα0).symm
  have h1 : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = ζ ^ (χ σ).val * kummerRoot p F x := by
    rw [hyeq, map_mul, hσε, hσα]; ring
  have h2 := kummerChar_spec p ζ hζ F x σ
  exact mul_right_cancel₀ hy0 (h2.symm.trans h1)

lemma exists_descend (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (χ : ↥K.fixingSubgroup → ZMod p) (hχ : ∀ σ τ : ↥K.fixingSubgroup, χ (σ * τ) = χ σ + χ τ)
    (hχL : ∀ σ : ↥K.fixingSubgroup, (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → χ σ = 0) :
    ∃ χbar : LevelGal K L hKL → ZMod p, (∀ g h, χbar (g * h) = χbar g + χbar h) ∧
      ∀ γ : ↥K.fixingSubgroup, χbar (levelGal K L hKL γ) = χ γ := by
  have hπsurj := levelGal_surjective K L hKL
  have hχ1 : χ 1 = 0 := by
    have h := hχ 1 1; rw [one_mul] at h; exact left_eq_add.mp h
  have hχinv : ∀ σ, χ σ⁻¹ = - χ σ := by
    intro σ; have h := hχ σ⁻¹ σ; rw [inv_mul_cancel, hχ1] at h; exact eq_neg_of_add_eq_zero_left h.symm
  have hχfib : ∀ γ γ' : ↥K.fixingSubgroup, levelGal K L hKL γ = levelGal K L hKL γ' → χ γ = χ γ' := by
    intro γ γ' h
    have h1 : levelGal K L hKL (γ⁻¹ * γ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : χ (γ⁻¹ * γ') = 0 := hχL _ (mem_fixingSubgroup_of_levelGal_eq_one K L hKL _ h1)
    rw [hχ, hχinv] at h2
    exact neg_add_eq_zero.mp h2
  refine ⟨fun g => χ (Function.surjInv hπsurj g), fun g h => ?_, fun γ => hχfib _ _ (Function.surjInv_eq hπsurj _)⟩
  obtain ⟨γ, rfl⟩ := hπsurj g; obtain ⟨δ, rfl⟩ := hπsurj h
  show χ (Function.surjInv hπsurj (levelGal K L hKL γ * levelGal K L hKL δ)) =
    χ (Function.surjInv hπsurj (levelGal K L hKL γ)) + χ (Function.surjInv hπsurj (levelGal K L hKL δ))
  rw [← map_mul, hχfib _ _ (Function.surjInv_eq hπsurj _), hχfib _ _ (Function.surjInv_eq hπsurj _),
    hχfib _ _ (Function.surjInv_eq hπsurj _), hχ]

lemma exists_root_of_level (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    [FiniteDimensional ℚ ↥L]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (χbar : LevelGal K L hKL → ZMod p) (hmul : ∀ g h, χbar (g * h) = χbar g + χbar h) :
    ∃ x : (↥K)ˣ, ∃ α : AlgebraicClosure ℚ, α ^ p = ((x : ↥K) : AlgebraicClosure ℚ) ∧
      ∀ γ : ↥K.fixingSubgroup, (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) α = ζ ^ (χbar (levelGal K L hKL γ)).val * α := by
  have hp : p.Prime := Fact.out
  haveI : FiniteDimensional ↥K ↥(levelField K L hKL) := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsGalois ↥K ↥(levelField K L hKL) := IsGalois.mk

  have hζL : ζ ∈ (levelField K L hKL) := (IntermediateField.mem_extendScalars hKL).2 (hKL hζK)
  have hζ0 : (⟨ζ, hζL⟩ : ↥(levelField K L hKL)) ≠ 0 := fun h => hζ.ne_zero hp.ne_zero (congrArg Subtype.val h)
  have hζpow : (Units.mk0 _ hζ0) ^ p = 1 := by
    apply Units.ext; apply Subtype.ext
    show ζ ^ p = 1
    exact hζ.pow_eq_one
  have hμK : ∀ m : ↥(rootsOfUnity p ↥(levelField K L hKL)), (((m : (↥(levelField K L hKL))ˣ) : ↥(levelField K L hKL)) : AlgebraicClosure ℚ) ∈ K := by
    intro m
    have hm : ((((m : (↥(levelField K L hKL))ˣ) : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) ^ p = 1 := by
      have h := (mem_rootsOfUnity p (m : (↥(levelField K L hKL))ˣ)).1 m.2
      have h2 := congrArg (fun u : (↥(levelField K L hKL))ˣ => ((u : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) h
      simpa using h2
    exact CycBaseKummer.mem_of_pow_eq_one p ζ hζ K hζK hm
  have hfixμ : ∀ (g : LevelGal K L hKL) (m : ↥(rootsOfUnity p ↥(levelField K L hKL))), g • m = m :=
    smul_rootsOfUnity_eq_self (fun m => ⟨⟨_, hμK m⟩, rfl⟩)

  have hc : groupCohomology.IsMulCocycle₁
      (fun g : LevelGal K L hKL => (⟨Units.mk0 _ hζ0, (mem_rootsOfUnity p _).2 hζpow⟩ : ↥(rootsOfUnity p ↥(levelField K L hKL))) ^
        (χbar g).val) := by
    intro g h
    dsimp only
    rw [hfixμ, hmul, pow_val_add' (Subtype.ext hζpow), mul_comm]

  obtain ⟨a, ha⟩ := groupCohomology.Kummer.kummerHom_surjective (K := ↥K) (L := ↥(levelField K L hKL)) p
    (Multiplicative.ofAdd (groupCohomology.H1π _ (groupCohomology.cocyclesOfIsMulCocycle₁ hc)))
  have hα := groupCohomology.Kummer.chosenRoot_spec a
  rw [groupCohomology.Kummer.kummerHom_apply] at ha
  have hcoc := kummerCocycleRoots_eq_of_kummerClass_eq hfixμ hα hc (Multiplicative.ofAdd.injective ha)
  refine ⟨(a : (↥K)ˣ), (((groupCohomology.Kummer.chosenRoot a : (↥(levelField K L hKL))ˣ) : ↥(levelField K L hKL)) : AlgebraicClosure ℚ), ?_, fun γ => ?_⟩
  · have h := congrArg (fun z : ↥(levelField K L hKL) => (z : AlgebraicClosure ℚ)) hα
    simp only [SubmonoidClass.coe_pow] at h
    exact h.symm
  · have hg1 : ((groupCohomology.Kummer.kummerCocycleRoots hα (levelGal K L hKL γ) : ↥(rootsOfUnity p ↥(levelField K L hKL))) : (↥(levelField K L hKL))ˣ) =
        (Units.mk0 _ hζ0) ^ (χbar (levelGal K L hKL γ)).val := by
      rw [hcoc]; rfl
    rw [groupCohomology.Kummer.coe_kummerCocycleRoots, groupCohomology.Kummer.kummerCocycle_apply, div_eq_iff_eq_mul] at hg1
    have hg2 := congrArg (fun u : (↥(levelField K L hKL))ˣ => ((u : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) hg1
    simp only [groupCohomology.Kummer.val_smul_units, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
      MulMemClass.coe_mul, SubmonoidClass.coe_pow, levelGal_apply_coe] at hg2
    exact hg2

end CycBaseKummerSurj

theorem solution
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hζF : ζ ∈ F)
    (χ : ↥F.fixingSubgroup → ZMod p) (hχ : ∀ σ τ : ↥F.fixingSubgroup, χ (σ * τ) = χ σ + χ τ)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F₀] (hF₀ : F ≤ F₀)
    (hχ₀ : ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup → χ σ = 0) :
    ∃ x : (↥F)ˣ, ∀ σ : ↥F.fixingSubgroup, kummerChar p ζ hζ F x σ = χ σ := by

  have hF₀E : F₀ ≤ IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ) := IntermediateField.le_normalClosure F₀
  have hFE : F ≤ IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ) := hF₀.trans hF₀E
  haveI : FiniteDimensional ℚ ↥(IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ)) :=
    normalClosure.is_finiteDimensional ℚ (↥F₀) _
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ)) := normalClosure.normal ℚ (↥F₀) _
  have hEn := CycBaseKummerSurj.fixingSubgroup_normal (IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ))
  have hnorm : IsNormalLevel F (IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ)) :=
    fun g _ s hs => hEn.conj_mem s hs g
  haveI hN : Normal ↥F ↥(levelField F (IntermediateField.normalClosure ℚ (↥F₀) (AlgebraicClosure ℚ)) hFE) :=
    NumberField.LevelArith.normal_levelField_of_isNormalLevel F _ hFE hnorm

  obtain ⟨χbar, hmul, hχbar⟩ := CycBaseKummerSurj.exists_descend F _ hFE χ hχ
    (fun σ hσ => hχ₀ σ (IntermediateField.fixingSubgroup_antitone hF₀E hσ))
  obtain ⟨x, α, hαp, hσα⟩ := CycBaseKummerSurj.exists_root_of_level F _ hFE ζ hζ hζF χbar hmul
  exact ⟨x, fun σ => CycBaseKummerSurj.kummerChar_eq_of_apply_root ζ hζ F hζF χ x α hαp
    (fun τ => by rw [hσα τ, hχbar τ]) σ⟩

end S_NumberField_LevelArith_exists_kummerChar_eq_of_continuous
end P2MW
export P2MW.S_NumberField_LevelArith_exists_kummerChar_eq_of_continuous (solution)
