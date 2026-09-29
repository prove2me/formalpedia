-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/57454294-0ed2-5068-b0f5-69c13fec216f

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_LocalBridge
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
import Theorems.Thm_NumberField_PlaceDecomp_exists_unit_localInv_eq_mul_of_inflate_eq_kummer
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_Rep_isEquivariantBilinear_eval_dualTwist
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_ExtCitation_LocalLevel_exists_intermediateField_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index
import Theorems.Thm_NumberField_natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped NumberField.PlaceDecomp

namespace IDLOCPlumb

section torsionHelper

lemma zsmul_hom4_eq_zero {M₀ M₁ M₂ M₃ M₄ : ModuleCat.{0} ℤ} (f₁ : M₀ ⟶ M₁) (f₂ : M₁ ⟶ M₂) (f₃ : M₂ ⟶ M₃) (f₄ : M₃ ⟶ M₄)
    (n : M₀) (c : ℤ) (hn : c • n = 0) : c • f₄.hom (f₃.hom (f₂.hom (f₁.hom n))) = 0 := by
  rw [← map_zsmul f₄.hom, ← map_zsmul f₃.hom, ← map_zsmul f₂.hom, ← map_zsmul f₁.hom, hn, map_zero, map_zero, map_zero, map_zero]

lemma lin2_smul {k : Type*} [CommRing k] {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (f : M →ₗ[k] N) (g : N →ₗ[k] k) (c : k) (x : M) : g (f (c • x)) = c * g (f x) := by
  rw [map_smul, map_smul, smul_eq_mul]
lemma hom_zsmul_nsmul {X Y : ModuleCat.{0} ℤ} (f : X ⟶ Y) (k : ℤ) (n : ℕ) (x : X) :
    f.hom (k • (n • x)) = k • (n • f.hom x) := by
  rw [map_zsmul, map_nsmul]
lemma addMonoidHom_zsmul_nsmul {X : ModuleCat.{0} ℤ} {B : Type*} [AddCommGroup B] (g : X →+ B) (k : ℤ) (n : ℕ) (x : X) :
    g (k • (n • x)) = k • (n • g x) := by
  rw [map_zsmul, map_nsmul]

lemma addCircle_arith (p : ℕ) [Fact p.Prime] (N d : ℕ) (hd : N = p * d) (hN : 0 < N) (k : ℤ) :
    (((k • ((N / p) • ((1:ℚ) / (N:ℚ)))) : ℚ) : AddCircle (1:ℚ)) =
      (((((k : ZMod p)).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  have hdp : N / p = d := by rw [hd]; exact Nat.mul_div_cancel_left d (Fact.out : p.Prime).pos
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [hd] at hN
    exact_mod_cast (Nat.pos_of_mul_pos_left hN).ne'
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hval : (((k : ZMod p)).val : ℚ) = ((k % p : ℤ) : ℚ) := by exact_mod_cast ZMod.val_intCast (n := p) k
  rw [hdp, hval, Int.emod_def, eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨-(k / p), ?_⟩
  have h1 : (d : ℚ) • ((1:ℚ) / (N:ℚ)) = (p : ℚ)⁻¹ := by
    rw [hd, Nat.cast_mul, smul_eq_mul, one_div, mul_inv, mul_comm (p:ℚ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
  rw [← Nat.cast_smul_eq_nsmul ℚ, h1, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  push_cast
  rw [sub_div, mul_div_cancel_left₀ _ hp0, div_eq_mul_inv]
  ring

lemma addCircle_arith' (p : ℕ) [Fact p.Prime] (N m a : ℕ) (hN : m * p ^ (a + 1) = N) (hN0 : 0 < N) (k : ℤ) :
    k • (p ^ a • ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ))) =
      (((((k : ZMod p)).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; rw [zero_mul] at hN; omega
    exact_mod_cast this
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hval : (((k : ZMod p)).val : ℚ) = ((k % p : ℤ) : ℚ) := by exact_mod_cast ZMod.val_intCast (n := p) k
  have h1 : p ^ a • ((m : ℚ) / (N : ℚ)) = (p : ℚ)⁻¹ := by
    rw [← hN, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, pow_succ]
    field_simp
  rw [← AddCircle.coe_nsmul, ← AddCircle.coe_zsmul, h1, hval, Int.emod_def, eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub,
    AddCircle.coe_eq_zero_iff]
  refine ⟨-(k / p), ?_⟩
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
  push_cast
  rw [sub_div, mul_div_cancel_left₀ _ hp0, div_eq_mul_inv]
  ring
end torsionHelper

section generic
universe u
variable {k : Type u} [CommRing k] {Γ H : Type u} [Group Γ] [Group H]

noncomputable def resCocycle₁ (r : H →* Γ) (A : Rep k Γ) (c : cocycles₁ A) : cocycles₁ (Rep.res r A) :=
  ⟨fun h => c (r h), (mem_cocycles₁_iff _).2 fun g h => by
    have := (mem_cocycles₁_iff (⇑c)).1 c.2 (r g) (r h)
    simpa [map_mul] using this⟩

@[scoped simp] lemma resCocycle₁_apply (r : H →* Γ) (A : Rep k Γ) (c : cocycles₁ A) (h : H) :
    resCocycle₁ r A c h = c (r h) := rfl

lemma H1π_resCocycle₁ (r : H →* Γ) (A : Rep k Γ) (c : cocycles₁ A) :
    (H1π (Rep.res r A)).hom (resCocycle₁ r A c) = (map r (𝟙 (Rep.res r A)) 1).hom ((H1π A).hom c) := by
  rw [H1π_comp_map_apply]
  congr 1

lemma isLevelConstant₁_res_of_factors {X : Type*} (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F]
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) (c₀ : (F ≃ₐ[ℚ] F) → X)
    (hc : ∀ γ, c γ = c₀ (AlgEquiv.restrictNormalHom F γ)) :
    IsLevelConstant₁ r (fun h => c (r h)) := by
  refine ⟨F, inferInstance, fun g s hs => ?_⟩
  simp only [hc, map_mul]
  congr 1
  have : AlgEquiv.restrictNormalHom F (r s) = 1 := by
    ext x
    have hx := (IntermediateField.mem_fixingSubgroup_iff F (r s)).1 hs x x.2
    rw [AlgEquiv.one_apply]
    exact (AlgEquiv.restrictNormal_commutes (r s) F x).trans hx
  rw [this, mul_one]

section cupLevel
variable {A B N : Rep k H}

omit [Group Γ] in

lemma restrictNormalHom_eq_one_of_mem_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    {γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hγ : γ ∈ F.fixingSubgroup) :
    AlgEquiv.restrictNormalHom F γ = 1 := by
  ext x
  rw [AlgEquiv.one_apply]
  exact (AlgEquiv.restrictNormal_commutes γ F x).trans ((IntermediateField.mem_fixingSubgroup_iff F γ).1 hγ x x.2)

omit [Group Γ] in

lemma isLevelConstant₂_cupCochain (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : A →ₗ[k] B →ₗ[k] N) (f : H → A) (hf : IsLevelConstant₁ r f) (g : cocycles₁ B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F]
    (c₀ : (F ≃ₐ[ℚ] F) → B) (hg : ∀ h, g h = c₀ (AlgEquiv.restrictNormalHom F (r h))) :
    IsLevelConstant₂ r (cupCochain φ f (⇑g)) := by
  obtain ⟨F₁, hF₁, h₁⟩ := hf
  haveI := hF₁
  refine ⟨F ⊔ F₁, IntermediateField.finiteDimensional_sup F F₁, fun a a' s s' hs hs' => ?_⟩
  have hsF : r s ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs'F : r s' ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs'
  have hsF₁ : r s ∈ F₁.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_right hs

  have hg_right : g (a' * s') = g a' := by
    rw [hg, hg, map_mul, map_mul, restrictNormalHom_eq_one_of_mem_fixingSubgroup F hs'F, mul_one]
  have hg_s : g s = 0 := by
    have h0 : g 1 = 0 := cocycles₁_map_one g
    rw [hg, map_one, map_one] at h0
    rw [hg, restrictNormalHom_eq_one_of_mem_fixingSubgroup F hsF]
    exact h0
  have hρ : B.ρ s (g a') = g a' := by
    have hc := (mem_cocycles₁_iff (⇑g)).1 g.2 s a'
    have hleft : g (s * a') = g a' := by
      rw [hg, hg, map_mul, map_mul, restrictNormalHom_eq_one_of_mem_fixingSubgroup F hsF, one_mul]
    rw [hleft, hg_s, add_zero] at hc
    exact hc.symm
  simp only [cupCochain_apply, h₁ a s hsF₁, hg_right, map_mul, Module.End.mul_apply, hρ]

noncomputable def cupLevelCocycle₂ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f)) (g : cocycles₁ B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F]
    (c₀ : (F ≃ₐ[ℚ] F) → B) (hg : ∀ h, g h = c₀ (AlgEquiv.restrictNormalHom F (r h))) :
    levelCocycles₂ r N :=
  ⟨cupCochain φ (⇑f) (⇑g), (mem_levelCocycles₂_iff r N _).2
    ⟨by rw [← cup_coe φ hφ f g]; exact (cup φ hφ f g).2, isLevelConstant₂_cupCochain r φ (⇑f) hf g F c₀ hg⟩⟩

lemma cupLevelCocycle₂_apply (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : A →ₗ[k] B →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear A B N φ)
    (f : cocycles₁ A) (hf : IsLevelConstant₁ r (⇑f)) (g : cocycles₁ B)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F]
    (c₀ : (F ≃ₐ[ℚ] F) → B) (hg : ∀ h, g h = c₀ (AlgEquiv.restrictNormalHom F (r h))) (st : H × H) :
    (cupLevelCocycle₂ r φ hφ f hf g F c₀ hg : H × H → N) st = cupCochain φ (⇑f) (⇑g) st := rfl

end cupLevel

end generic

section kummer
variable (p : ℕ) [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

noncomputable def zetaUnit (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) : (PadicAlgCl q)ˣ :=
  Units.map (padicEmbedding q : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q).toMonoidHom
    (hζ.isUnit (Fact.out : p.Prime).ne_zero).unit

lemma coe_zetaUnit (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ((zetaUnit p q ζ hζ : (PadicAlgCl q)ˣ) : PadicAlgCl q) = padicEmbedding q ζ := rfl

lemma zetaUnit_pow_p (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) : zetaUnit p q ζ hζ ^ p = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, coe_zetaUnit, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one]

lemma smul_zetaUnit (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (g : primeLocalGaloisGroup q) :
    (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from g) • zetaUnit p q ζ hζ =
      zetaUnit p q ζ hζ ^ ((cycloChar p (primeLocalToGlobal q g) : ZMod p)).val := by
  ext
  rw [AlgEquiv.smul_units_def, Units.coe_map, Units.val_pow_eq_pow_val, coe_zetaUnit, MonoidHom.coe_coe]

  have h1 : (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from g) (padicEmbedding q ζ) =
      padicEmbedding q (primeLocalToGlobal q g ζ) := (padicEmbedding_localGaloisToGlobal q g ζ).symm
  rw [h1, ← map_pow]
  congr 1
  have hu : (hζ.isUnit (Fact.out : p.Prime).ne_zero).unit ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; ext; simp [hζ.pow_eq_one]
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    ((primeLocalToGlobal q g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) hu
  (first | exact this | simpa using this | (have h__ := this; simp at h__; exact h__))

noncomputable def kummerLevelCocycle₂ (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (e : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by
  let U := zetaUnit p q ζ hζ
  let Ef : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
    fun st => Additive.ofMul (U ^ (((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) st).val))
  refine ⟨Ef, (mem_levelCocycles₂_iff _ _ _).2 ⟨?_, ?_⟩⟩
  ·
    have hUp : U ^ p = 1 := zetaUnit_pow_p p q ζ hζ
    have he := (mem_cocycles₂_iff (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)).1
      ((mem_levelCocycles₂_iff _ _ _).1 e.2).1
    rw [mem_cocycles₂_iff]
    intro g h j
    have hval := congrArg ZMod.val (he g h j)

    have hact : ((ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))).ρ g
        ((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p) (h, j))) =
        ((cycloChar p (primeLocalToGlobal q g) : ZMod p)) * (e : _ → ZMod p) (h, j) := by
      rfl
    rw [hact, ZMod.val_add, ZMod.val_add, ZMod.val_mul] at hval

    show (Additive.ofMul (U ^ ((e : _ → ZMod p) (g * h, j)).val) + Additive.ofMul (U ^ ((e : _ → ZMod p) (g, h)).val) :
        Additive (PadicAlgCl q)ˣ) =
      Additive.ofMul ((show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from g) • Additive.toMul (Additive.ofMul (U ^ ((e : _ → ZMod p) (h, j)).val)))
        + Additive.ofMul (U ^ ((e : _ → ZMod p) (g, h * j)).val)
    rw [← ofMul_mul, ← ofMul_mul, toMul_ofMul, smul_pow', smul_zetaUnit p q ζ hζ g, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    rw [pow_eq_pow_mod _ hUp, hval, ← pow_eq_pow_mod _ hUp]
    rw [pow_add, pow_add, ← pow_eq_pow_mod _ hUp]
  · exact ((mem_levelCocycles₂_iff _ _ _).1 e.2).2.comp (fun c : ZMod p => (Additive.ofMul (U ^ c.val) : Additive (PadicAlgCl q)ˣ))

lemma coe_toMul_kummerLevelCocycle₂ (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (e : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (g h : primeLocalGaloisGroup q) :
    ((Additive.toMul ((kummerLevelCocycle₂ p q ζ hζ e : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h) : ZMod p).val) := by
  show ((zetaUnit p q ζ hζ ^ _ : (PadicAlgCl q)ˣ) : PadicAlgCl q) = _
  rw [Units.val_pow_eq_pow_val, coe_zetaUnit]

lemma kummerLevelCocycle₂_smul (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (c : ZMod p)
    (e : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :
    kummerLevelCocycle₂ p q ζ hζ (c • e) = (c.val : ℤ) • kummerLevelCocycle₂ p q ζ hζ e := by
  apply Subtype.ext
  funext st
  have hUp := zetaUnit_pow_p p q ζ hζ
  show (Additive.ofMul (zetaUnit p q ζ hζ ^ ((c • (e : _ → ZMod p)) st).val) : Additive (PadicAlgCl q)ˣ) =
    (c.val : ℤ) • (Additive.ofMul (zetaUnit p q ζ hζ ^ (((e : _ → ZMod p)) st).val) : Additive (PadicAlgCl q)ˣ)
  rw [Pi.smul_apply, smul_eq_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hUp, ← ofMul_zpow, zpow_natCast, ← pow_mul, mul_comm]

end kummer

section inflate
variable (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

lemma restrictNormalHom_eq_one_of_mem_fixingSubgroup'
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    {γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hγ : γ ∈ F.fixingSubgroup) :
    AlgEquiv.restrictNormalHom F γ = 1 := by
  ext x
  rw [AlgEquiv.one_apply]
  exact (AlgEquiv.restrictNormal_commutes γ F x).trans ((IntermediateField.mem_fixingSubgroup_iff F γ).1 hγ x x.2)

lemma coord_eq_one_of_mem_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    {τ : primeLocalGaloisGroup q} (hτ : primeLocalToGlobal q τ ∈ F.fixingSubgroup) : π τ = 1 := by
  haveI : Normal ℚ ↥F := inferInstance
  apply Subtype.ext
  rw [hπ, OneMemClass.coe_one]
  apply restrictNormalHom_eq_one_of_mem_fixingSubgroup' F
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  intro x hx
  have hσx : σ x ∈ F := by
    have h := AlgEquiv.restrictNormal_commutes σ F ⟨x, hx⟩

    change ((σ.restrictNormal F ⟨x, hx⟩ : F) : AlgebraicClosure ℚ) = σ x at h
    rw [← h]
    exact SetLike.coe_mem _
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτ (σ x) hσx]
  exact (AlgEquiv.symm_apply_apply σ x : σ.symm (σ x) = x)

set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def inflateUnitsLevelCocycle₂
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hcompat : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) :
    levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := by

  let ι : Additive (w.adicCompletion ↥F)ˣ →+ Additive (PadicAlgCl q)ˣ :=
    (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive
  have hι : ∀ (τ : primeLocalGaloisGroup q) (u : (w.adicCompletion ↥F)ˣ),
      ι (Additive.ofMul (π τ • u)) = Additive.ofMul ((show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) • Additive.toMul (ι (Additive.ofMul u))) := by
    intro τ u
    apply Additive.toMul.injective
    ext
    simp only [ι, MonoidHom.toAdditive_apply_apply, toMul_ofMul, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def,
      NumberField.PlaceDecomp.coe_smul_units, hcompat]
  let Xf : primeLocalGaloisGroup q × primeLocalGaloisGroup q → Additive (PadicAlgCl q)ˣ :=
    fun st => ι ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π st.1, π st.2))
  refine ⟨Xf, (mem_levelCocycles₂_iff _ _ _).2 ⟨?_, ?_⟩⟩
  · rw [mem_cocycles₂_iff]
    intro g h j
    have hx := (mem_cocycles₂_iff (x : _ → Additive (w.adicCompletion ↥F)ˣ)).1 x.2 (π g) (π h) (π j)
    have key : ι ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π g * π h, π j)) + ι ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π g, π h)) =
        ι (((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ).ρ (π g))
            ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π h, π j))) + ι ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π g, π h * π j)) :=
      (ι.map_add _ _).symm.trans ((congrArg ι hx).trans (ι.map_add _ _))
    show Xf (g * h, j) + Xf (g, h) = Additive.ofMul ((show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from g) • Additive.toMul (Xf (h, j))) + Xf (g, h * j)
    simp only [Xf, map_mul]
    refine key.trans ?_
    congr 1
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
    exact hι g (Additive.toMul ((x : _ → Additive (w.adicCompletion ↥F)ˣ) (π h, π j)))
  · refine ⟨F, inferInstance, fun g g' s s' hs hs' => ?_⟩
    simp only [Xf, map_mul, coord_eq_one_of_mem_fixingSubgroup q F w σ π hπ hs, coord_eq_one_of_mem_fixingSubgroup q F w σ π hπ hs',
      mul_one]

lemma toMul_inflateUnitsLevelCocycle₂
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hcompat : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))
    (g h : primeLocalGaloisGroup q) :
    Additive.toMul ((inflateUnitsLevelCocycle₂ q F w σ Φ π hπ hcompat x : primeLocalGaloisGroup q × primeLocalGaloisGroup q →
        (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)
        (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h))) := rfl

end inflate

section theta
universe u
variable {k G : Type u} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (inv : continuousH2 r N →ₗ[k] k)

lemma theta1_eq_inv_cup (θ : continuousH1 r M →ₗ[k] Module.Dual k (continuousH1 r D)) (hθ : IsTheta1 r φ inv θ)
    (f : cocycles₁ M) (hf : IsLevelConstant₁ r (⇑f)) (g : cocycles₁ D) (hg : IsLevelConstant₁ r (⇑g))
    (e : levelCocycles₂ r N) (he : ∀ st, (e : G × G → N) st = cupCochain φ (⇑f) (⇑g) st)
    (z : continuousH1 r M) (hz : (z : H1 M) = (H1π M).hom f)
    (w : continuousH1 r D) (hw : (w : H1 D) = (H1π D).hom g) :
    θ z w = inv (continuousH2π r N e) := by
  have h := hθ f hf g hg e he
  have hz' : z = ⟨(H1π M).hom f, H1π_mem_continuousH1 r M hf⟩ := Subtype.ext hz
  have hw' : w = ⟨(H1π D).hom g, H1π_mem_continuousH1 r D hg⟩ := Subtype.ext hw
  subst hz' hw'
  exact h

end theta

section bridge

lemma natPrime_eq_of_mem_asIdeal {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {ℓ q : ℕ} (hℓ : ℓ.Prime) (hq : q.Prime) (h1 : ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    ℓ = q := by
  by_contra hne
  have hcop : IsCoprime (ℓ : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes hℓ hq).2 hne
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((a : 𝓞 K) * (ℓ : ℕ) + (b : 𝓞 K) * (q : ℕ) : 𝓞 K) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) hab
  rw [← this]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)

noncomputable def unitsBridgeHom {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (hcompat : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (hΦ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y) :
    Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (Representation.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)
    (Representation.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    ((Units.map (Φ.symm : L →* w.adicCompletion K)).toAdditive.toIntLinearMap) (fun g v => by
      apply Additive.toMul.injective
      ext
      simp only [AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, Representation.ofMulDistribMulAction_apply_apply,
        toMul_ofMul, Units.coe_map, MonoidHom.coe_coe, NumberField.PlaceDecomp.coe_smul_units, hcompat]
      apply Φ.injective
      rw [hΦ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]))

lemma coe_toMul_unitsBridgeHom {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (hcompat : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (hΦ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y) (y : (↥L)ˣ) :
    ((Additive.toMul ((unitsBridgeHom w L Φ hcompat hΦ).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L) :=
  rfl

end bridge

end IDLOCPlumb
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary.IDLOCPlumb"

set_option maxHeartbeats 48000000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : (ZMod p)ˣ,
    ∀ (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))

    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (_ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (_ : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (_ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (_ : Function.Surjective π)
    (_ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

    (T : ShortComplex (Rep ℤ (↥F ≃ₐ[ℚ] ↥F))) (hT : T.ShortExact)
    (hTD : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).ShortExact)
    (_ : ∀ b : T.X₃, p • b = 0)
    (κ : T.X₃ →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (_ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : T.X₃) (m : M),
      κ (T.X₃.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (_ : ∀ c : T.X₃ →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (β : T.X₃ →+ M.dualTwist (cycloChar p))
    (_ : ∀ (b : T.X₃) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)
    (κq : T.X₃ →+ M →+ Additive (PadicAlgCl q)ˣ)
    (_ : ∀ (b : T.X₃) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))

    (D : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F)
    [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)]
    (_ : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F), g • c = D.classAct g c)
    (ι : (w.adicCompletion ↥F)ˣ →* (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (_ : ∀ x : (w.adicCompletion ↥F)ˣ,
      finPart w (ι x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 ↥F), w' ≠ w → finPart w' (ι x) = 1) ∧ infPart (ι x) = 1)
    (lam : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)))
    (_ : ∀ x : (w.adicCompletion ↥F)ˣ,
      lam.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι x) : IdeleClassGroup (𝓞 ↥F) ↥F))

    (invD : ↥(groupCohomology (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
        (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F))) 2) →+ AddCircle (1 : ℚ))
    (_ : Function.Injective invD)
    (_ : ∀ (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ' : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • invD
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) lam 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M))
    (_ : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.f) ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (θq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (_ : IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θq)

    (aw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (n : cocycles₁ T.X₃) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (_ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))
    (zq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (_ : (zq : H1 (Rep.res (extArithLoc S (Sum.inr q)) M)) = Λq aw)
    (wq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))
    (_ : (wq : H1 (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom ((H1π (M.dualTwist (cycloChar p))).hom ny)),
    invD ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (aw ≫ lam) 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n))))
      = ((((((u : ZMod p) * θq zq wq).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
  classical
  obtain ⟨u₁, h₁⟩ :=
    NumberField.PlaceDecomp.exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant S q ζ hζ
  obtain ⟨u₂, h₂⟩ :=
    NumberField.PlaceDecomp.exists_unit_localInv_eq_mul_of_inflate_eq_kummer (p := p) (q : Nat.Primes) ζ hζ
  refine ⟨u₁ * u₂⁻¹, ?_⟩
  intro M F _ _ w σ Φ hb1 hb2 π hb3 hb4 hb5 T hT hTD hb6 κ hb7 hb8 β hb9 κq hb10 Dd _ hb11 ιw hb12 lam hb13 invD hb14 hb15
    Λq hb22 θq hb23 aw n ny hb24 zq hb25 wq hb26

  obtain ⟨fq, hfq, hfqz⟩ := (mem_continuousH1_iff _ _ _).1 zq.2
  have hfqΛ : (H1π (Rep.res (primeLocalToGlobal q) M)).hom fq = Λq aw := hfqz.trans hb25
  let gq : cocycles₁ (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) :=
    IDLOCPlumb.resCocycle₁ (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) ny
  have hgq : ∀ τ : primeLocalGaloisGroup q, gq τ = ny (primeLocalToGlobal q τ) := fun τ => rfl
  haveI : Normal ℚ ↥F := inferInstance
  let c₀ : (↥F ≃ₐ[ℚ] ↥F) → Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) :=
    fun d => (β (n d) : M.dualTwist (cycloChar p))
  have hgq' : ∀ h : extArithLocalGroups S (Sum.inr q), gq h = c₀ (AlgEquiv.restrictNormalHom ↥F (extArithLoc S (Sum.inr q) h)) :=
    fun τ => hb24 _

  have hφ : Rep.IsEquivariantBilinear (Rep.res (extArithLoc S (Sum.inr q)) M) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))
      (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))
      (Module.Dual.eval (ZMod p) M :
          Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p]
            Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p] (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) :=
    fun g a b => Rep.isEquivariantBilinear_eval_dualTwist M (cycloChar p) (primeLocalToGlobal q g) a b
  let e := IDLOCPlumb.cupLevelCocycle₂ (extArithLoc S (Sum.inr q)) _ hφ fq hfq gq F c₀ hgq'
  let E := IDLOCPlumb.kummerLevelCocycle₂ p (q : Nat.Primes) ζ hζ e

  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))).1
    inferInstance
    ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) aw 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n))))
  let X := IDLOCPlumb.inflateUnitsLevelCocycle₂ (q : Nat.Primes) F w σ Φ π hb3 hb5 x

  have hBC := h₁ M F w σ Φ hb1 hb2 π hb3 hb4 hb5 T hT hTD hb6 κ hb7 hb8 β hb9 κq hb10 Λq hb22 aw n ny hb24 fq hfqΛ hfq gq hgq
    e (fun st => rfl) E (IDLOCPlumb.coe_toMul_kummerLevelCocycle₂ p (q : Nat.Primes) ζ hζ e) x hx X
    (IDLOCPlumb.toMul_inflateUnitsLevelCocycle₂ (q : Nat.Primes) F w σ Φ π hb3 hb5 x)

  have hgqlc : IsLevelConstant₁ (extArithLoc S (Sum.inr q)) (⇑gq) :=
    IDLOCPlumb.isLevelConstant₁_res_of_factors (extArithLoc S (Sum.inr q)) F (⇑ny)
      (fun d => (β (n d) : M.dualTwist (cycloChar p))) hb24
  have hθ : θq zq wq = localInv p ζ (q : Nat.Primes)
      (continuousH2π (extArithLoc S (Sum.inr q)) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) e) :=
    IDLOCPlumb.theta1_eq_inv_cup (extArithLoc S (Sum.inr q)) _ (localInv p ζ (q : Nat.Primes)) θq hb23 fq hfq gq hgqlc e
      (fun st => rfl) zq hfqz.symm wq
      (hb26.trans (IDLOCPlumb.H1π_resCocycle₁ (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) ny).symm)

  have hXE : continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) X =
      continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))
        (IDLOCPlumb.kummerLevelCocycle₂ p (q : Nat.Primes) ζ hζ ((u₁ : ZMod p) • e)) := by
    have hs := IDLOCPlumb.kummerLevelCocycle₂_smul p (q : Nat.Primes) ζ hζ (u₁ : ZMod p) e
    exact hBC.trans ((map_zsmul _ _ _).symm.trans (congrArg _ hs.symm))

  have hwq : (((q : Nat.Primes) : ℕ) : 𝓞 ↥F) ∈ w.asIdeal :=
    NumberField.natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl ((q : Nat.Primes) : ℕ) ↥F w Φ hb2
  have hbr := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion ℚ ↥F w
  obtain ⟨q₀, hbr⟩ := hbr
  obtain ⟨instq₀, hbr⟩ := hbr
  obtain ⟨L', hbr⟩ := hbr
  obtain ⟨instFD, hbr⟩ := hbr
  obtain ⟨instMSA, hbr⟩ := hbr
  obtain ⟨instFS, hbr⟩ := hbr
  obtain ⟨instMDA, hbr⟩ := hbr
  obtain ⟨Φb, hG', hcompat', hΦb, hq₀⟩ := hbr
  have hqq : q₀ = ((q : Nat.Primes) : ℕ) :=
    IDLOCPlumb.natPrime_eq_of_mem_asIdeal w (ℓ := q₀) (q := ((q : Nat.Primes) : ℕ)) instq₀.out Fact.out hq₀ hwq
  subst hqq
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) :=
    ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic _ L' _ hG'
  have hK := ExtCitation.LocalLevel.exists_intermediateField_forall_mem_iff_smul_eq ((q : Nat.Primes) : ℕ) L'
    ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) hG'
  obtain ⟨K₀, hK⟩ := hK
  obtain ⟨instK₀, hK₀le, hK₀⟩ := hK
  have hBase : ExtCitation.LocalLevel.IsBase ((q : Nat.Primes) : ℕ) L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀ := ⟨hK₀le, hK₀⟩
  have hu := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass ((q : Nat.Primes) : ℕ) L'
    ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) hG' hcompat' hsolv K₀ hBase
  let u' := hu.exists.choose
  have hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass ((q : Nat.Primes) : ℕ) L' ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) K₀ u' :=
    hu.exists.choose_spec
  let θ' := IDLOCPlumb.unitsBridgeHom (E := ℚ) (K := ↥F) w L' Φb hcompat' hΦb
  have hθ' := IDLOCPlumb.coe_toMul_unitsBridgeHom (E := ℚ) (K := ↥F) w L' Φb hcompat' hΦb

  let c := (groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
      (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n)
  let z := (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) aw 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom c)
  have hxz : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = z := hx
  have hn0 : (p : ℤ) • n = 0 := by
    apply Subtype.ext
    funext g
    show (p : ℤ) • n g = 0
    rw [natCast_zsmul]
    exact hb6 (n g)
  have hz0 := IDLOCPlumb.zsmul_hom4_eq_zero (H1π T.X₃)
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1)
      (groupCohomology.δ hTD 1 2 rfl)
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) aw 2) n (p : ℤ) hn0
  have hzm := NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass ℚ ↥F w hsolv ((q : Nat.Primes) : ℕ) L' Φb
    hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' z
  let m := hzm.choose
  have hm := hzm.choose_spec
  by_cases hpD : p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)
  ·
    have hpD' := hpD
    obtain ⟨d, hd⟩ := hpD'
    have hiff := NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ℚ ↥F w hsolv _ L' Φb
        hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' ((p : ℤ) * m)
    have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℤ) ∣ (p : ℤ) * m := by
      rw [← hiff, mul_zsmul, ← hm]
      exact hz0
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hdk : (d : ℤ) ∣ m := by
      rw [hd, Nat.cast_mul] at hdvd
      exact (mul_dvd_mul_iff_left hp0).1 hdvd
    let k : ℤ := hdk.choose
    have hk : m = d * k := hdk.choose_spec
    have hdp : Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) / p = d := by
      rw [hd]; exact Nat.mul_div_cancel_left d (Fact.out : p.Prime).pos
    change z = m • _ at hm
    rw [hk, mul_comm, mul_zsmul, natCast_zsmul, ← hdp] at hm

    have hLN := h₂ F w hpD σ Φ hb1 hb2 π hb3 hb4 hb5 L' Φb hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' k z hm x hxz X
      (IDLOCPlumb.toMul_inflateUnitsLevelCocycle₂ (q : Nat.Primes) F w σ Φ π hb3 hb5 x)
      ((u₁ : ZMod p) • e) (IDLOCPlumb.kummerLevelCocycle₂ p (q : Nat.Primes) ζ hζ ((u₁ : ZMod p) • e))
      (IDLOCPlumb.coe_toMul_kummerLevelCocycle₂ p (q : Nat.Primes) ζ hζ ((u₁ : ZMod p) • e)) hXE

    have hcs := IDLOCPlumb.lin2_smul (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
      (localInv p ζ (q : Nat.Primes)) (u₁ : ZMod p) e
    have hθk : (u₁ : ZMod p) * θq zq wq = (u₂ : ZMod p) * (k : ZMod p) := by
      rw [hθ, ← hLN]
      exact hcs.symm
    have hk' : ((u₁ * u₂⁻¹ : (ZMod p)ˣ) : ZMod p) * θq zq wq = (k : ZMod p) := by
      rw [Units.val_mul, mul_comm (u₁ : ZMod p), mul_assoc, hθk, ← mul_assoc, Units.inv_mul, one_mul]

    have hd0 : d ≠ 0 := by
      rintro rfl
      have : 0 < Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) := Nat.card_pos
      rw [hd, mul_zero] at this
      exact lt_irrefl 0 this
    obtain ⟨a, m, hpm, hdam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p (Fact.out : p.Prime).one_lt.ne'
    have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpm
    have hN : m * p ^ (a + 1) = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) := by rw [hd, hdam, pow_succ]; ring
    have hND := hb15 L' Φb hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' m a.succ hcop hN
    rw [groupCohomology.map_id_comp]
    change invD ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) lam 2).hom z) = _
    rw [hm, IDLOCPlumb.hom_zsmul_nsmul, IDLOCPlumb.addMonoidHom_zsmul_nsmul, hdp, hdam, mul_nsmul', hND, hk']

    exact IDLOCPlumb.addCircle_arith' p _ m a hN Nat.card_pos k
  ·

    have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℤ) ∣ (p : ℤ) * m := by
      rw [← NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ℚ ↥F w hsolv _ L' Φb
        hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' ((p : ℤ) * m), mul_zsmul, ← hm]
      exact hz0
    have hcopN : (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)).Coprime p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hpD)
    have hcop : IsCoprime (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcopN
    have hz : z = 0 := by
      change z = m • _ at hm
      rw [hm]
      exact (NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ℚ ↥F w hsolv _ L' Φb
        hG' hcompat' hΦb K₀ hBase θ' hθ' u' hu' m).2 (hcop.dvd_of_dvd_mul_left hdvd)

    have hker : ∀ τ : primeLocalGaloisGroup q, π τ = 1 → gq τ = 0 := by
      intro τ hτ
      have h1 : AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ) = 1 := by
        rw [← hb3, hτ]; rfl
      have h2 : AlgEquiv.restrictNormalHom ↥F (primeLocalToGlobal q τ) = 1 := by
        rw [map_mul, map_mul, map_inv] at h1
        calc AlgEquiv.restrictNormalHom ↥F (primeLocalToGlobal q τ)
            = AlgEquiv.restrictNormalHom ↥F σ *
                ((AlgEquiv.restrictNormalHom ↥F σ)⁻¹ * AlgEquiv.restrictNormalHom ↥F (primeLocalToGlobal q τ) *
                  AlgEquiv.restrictNormalHom ↥F σ) * (AlgEquiv.restrictNormalHom ↥F σ)⁻¹ := by group
          _ = 1 := by rw [h1]; group
      rw [hgq, hb24, h2, cocycles₁_map_one, map_zero]
    have hidxN : π.ker.index = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hb4, Subgroup.card_top]
    have hfi : π.ker.FiniteIndex := ⟨by rw [hidxN]; exact Nat.card_pos.ne'⟩
    have hidx : IsUnit ((π.ker.index : ZMod p)) := by
      rw [hidxN, ZMod.isUnit_iff_coprime]
      exact hcopN
    obtain ⟨a, ha⟩ := @groupCohomology.mem_coboundaries1_of_restrict_of_isUnit_index (ZMod p) (primeLocalGaloisGroup q) _ _
      (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))) π.ker hfi hidx gq
      ⟨0, fun s => by rw [map_zero, sub_zero]; exact hker s.1 (MonoidHom.mem_ker.1 s.2)⟩
    have hgq0 : (H1π (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))).hom gq = 0 :=
      (H1π_eq_zero_iff gq).2 ⟨a, funext fun g => (d₀₁_hom_apply _ a g).trans (ha g).symm⟩
    have hwq : wq = 0 := by
      rw [← Submodule.coe_eq_zero,
        hb26.trans (IDLOCPlumb.H1π_resCocycle₁ (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) ny).symm]
      exact hgq0

    rw [groupCohomology.map_id_comp]
    change invD ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) lam 2).hom z) = _
    rw [hz, map_zero, map_zero, hwq, map_zero, mul_zero, ZMod.val_zero, Nat.cast_zero, zero_div, AddCircle.coe_zero]

end S_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary (solution)
