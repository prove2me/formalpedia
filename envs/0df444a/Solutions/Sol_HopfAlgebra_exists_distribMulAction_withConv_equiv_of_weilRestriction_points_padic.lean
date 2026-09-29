-- Prove2me | solution 1 for HopfAlgebra.exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3ced104b-4009-51fb-ae4d-bac124291139

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic

set_option autoImplicit false
open scoped TensorProduct

namespace S17Ind

open scoped TensorProduct

variable (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B]
  (L : Type) [Field L] [Algebra R L]

noncomputable def Θ : L ⊗[R] B →ₐ[L] ((B →ₐ[R] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (Pi.algHom _ _ fun τ : B →ₐ[R] L => τ)
    (fun _ _ => Commute.all _ _)

@[scoped simp] theorem Θ_tmul (x : L) (b : B) (τ : B →ₐ[R] L) : Θ R B L (x ⊗ₜ[R] b) τ = x * τ b := by
  simp [Θ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Pi.algebraMap_apply]

noncomputable def fτ (τ : B →ₐ[R] L) : Module.Dual L (L ⊗[R] B) :=
  (LinearMap.proj τ).comp (Θ R B L).toLinearMap

theorem fτ_apply (τ : B →ₐ[R] L) (y : L ⊗[R] B) : fτ R B L τ y = Θ R B L y τ := rfl

noncomputable def res : Module.Dual L (L ⊗[R] B) →ₗ[L] (B → L) where
  toFun φ b := φ ((1 : L) ⊗ₜ[R] b)
  map_add' φ ψ := by funext b; rfl
  map_smul' a φ := by funext b; rfl

theorem res_fτ (τ : B →ₐ[R] L) : res R B L (fτ R B L τ) = (τ : B → L) := by
  funext b
  show fτ R B L τ ((1 : L) ⊗ₜ[R] b) = τ b
  rw [fτ_apply, Θ_tmul, one_mul]

theorem linearIndependent_fτ : LinearIndependent L (fτ R B L) := by
  have hinj : Function.Injective (fun τ : B →ₐ[R] L => (τ : B →* L)) := fun τ₁ τ₂ h =>
    AlgHom.ext fun b => DFunLike.congr_fun h b
  have hded : LinearIndependent L (fun τ : B →ₐ[R] L => ((τ : B →* L) : B → L)) :=
    (linearIndependent_monoidHom B L).comp _ hinj
  apply LinearIndependent.of_comp (res R B L)
  convert hded using 1
  funext τ
  exact res_fτ R B L τ

theorem finite_algHom [Module.Finite R B] : Finite (B →ₐ[R] L) :=
  (linearIndependent_fτ R B L).finite

theorem Θ_bijective [Nontrivial R] [Module.Finite R B] [Module.Free R B] [Fintype (B →ₐ[R] L)]
    (hcard : Fintype.card (B →ₐ[R] L) = Module.finrank R B) : Function.Bijective (Θ R B L) := by
  classical
  have hV : Module.finrank L (L ⊗[R] B) = Module.finrank R B := Module.finrank_baseChange
  have hcard' : Fintype.card (B →ₐ[R] L) = Module.finrank L (Module.Dual L (L ⊗[R] B)) := by
    rw [Subspace.dual_finrank_eq, hV, hcard]
  let bD : Module.Basis (B →ₐ[R] L) L (Module.Dual L (L ⊗[R] B)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_fτ R B L) hcard'
  have hbD' : ⇑bD = fτ R B L := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hbD : ∀ τ, bD τ = fτ R B L τ := fun τ => congrFun hbD' τ
  have hinj : Function.Injective (Θ R B L) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    rw [← Module.forall_dual_apply_eq_zero_iff L y]
    intro φ
    rw [← bD.linearCombination_repr φ, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun τ _ => ?_
    rw [LinearMap.smul_apply, hbD, fτ_apply, hy, Pi.zero_apply, smul_zero]
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank L (L ⊗[R] B) = Module.finrank L ((B →ₐ[R] L) → L) := by
    rw [hV, Module.finrank_fintype_fun_eq_card, hcard]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

end S17Ind
p2m_reactivate "P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic.S17Ind"

namespace S17Ind

open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable (B : Type) [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
  [Algebra B (AlgebraicClosure ℚ_[p])] [IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])]

local notation "𝕃" => AlgebraicClosure ℚ_[p]

noncomputable abbrev τ₀ : B →ₐ[ℤ_[p]] 𝕃 := IsScalarTower.toAlgHom ℤ_[p] B 𝕃

theorem algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[p] 𝕃) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] 𝕃]
  exact (algebraMap ℚ_[p] 𝕃).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem algHom_injective (τ : B →ₐ[ℤ_[p]] 𝕃) : Function.Injective τ := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hker : RingHom.ker τ.toRingHom = ⊥ := by
    haveI : (RingHom.ker τ.toRingHom).IsPrime := RingHom.ker_isPrime _
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [RingHom.comap_ker, eq_bot_iff]
    intro r hr
    rw [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] at hr
    exact (injective_iff_map_eq_zero _).mp (algebraMap_padicInt_injective p) r hr
  have : b ∈ RingHom.ker τ.toRingHom := hb
  rwa [hker, Ideal.mem_bot] at this

theorem card_algHom_and_transitive :
    ∃ _ : Fintype (B →ₐ[ℤ_[p]] 𝕃),
      Fintype.card (B →ₐ[ℤ_[p]] 𝕃) = Module.finrank ℤ_[p] B ∧
      ∀ τ : B →ₐ[ℤ_[p]] 𝕃, ∃ σ : 𝕃 ≃ₐ[ℚ_[p]] 𝕃, ∀ b : B, σ (algebraMap B 𝕃 b) = τ b := by
  classical
  haveI hfin : Finite (B →ₐ[ℤ_[p]] 𝕃) := finite_algHom ℤ_[p] B 𝕃
  letI : Fintype (B →ₐ[ℤ_[p]] 𝕃) := Fintype.ofFinite _
  refine ⟨inferInstance, ?_⟩

  let bB := Module.Free.chooseBasis ℤ_[p] B
  let d := Module.finrank ℤ_[p] B
  have hd : Fintype.card (Module.Free.ChooseBasisIndex ℤ_[p] B) = d := by
    convert (Module.finrank_eq_card_chooseBasisIndex ℤ_[p] B).symm
  let S : Set 𝕃 := Set.range fun i => τ₀ p B (bB i)
  let E : IntermediateField ℚ_[p] 𝕃 := IntermediateField.adjoin ℚ_[p] S

  have hint : ∀ x ∈ S, IsIntegral ℚ_[p] x := by
    rintro _ ⟨i, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ_[p]) (bB i)).map (τ₀ p B)).tower_top
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_adjoin hint

  have hmemE : ∀ b : B, τ₀ p B b ∈ E := by
    intro b
    rw [← bB.linearCombination_repr b, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] 𝕃]
    exact Subalgebra.mul_mem _ (E.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  let τE : B →ₐ[ℤ_[p]] E :=
    { toFun := fun b => ⟨τ₀ p B b, hmemE b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun r => Subtype.ext (by
        show τ₀ p B (algebraMap ℤ_[p] B r) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] 𝕃]
        rfl) }
  have hτE : ∀ b, (τE b : 𝕃) = τ₀ p B b := fun _ => rfl

  have hli𝕃 : LinearIndependent ℤ_[p] (fun i => τ₀ p B (bB i)) :=
    (bB.linearIndependent.map' (τ₀ p B).toLinearMap
      (LinearMap.ker_eq_bot.mpr (algHom_injective p B (τ₀ p B))))
  have hliQ : LinearIndependent ℚ_[p] (fun i => τ₀ p B (bB i)) :=
    (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp hli𝕃
  have hliE : LinearIndependent ℚ_[p] (fun i => (τE (bB i) : E)) := by
    apply LinearIndependent.of_comp (E.val.toLinearMap)
    exact hliQ
  have hdE : d ≤ Module.finrank ℚ_[p] E := by
    rw [← hd]
    exact hliE.fintype_card_le_finrank

  let res : (E →ₐ[ℚ_[p]] 𝕃) → (B →ₐ[ℤ_[p]] 𝕃) := fun χ => (χ.restrictScalars ℤ_[p]).comp τE
  have hres : Function.Injective res := by
    intro χ₁ χ₂ h
    apply IntermediateField.adjoin_algHom_ext ℚ_[p]
    rintro _ ⟨i, rfl⟩
    have := AlgHom.congr_fun h (bB i)
    exact this

  have hcardE : Fintype.card (E →ₐ[ℚ_[p]] 𝕃) = Module.finrank ℚ_[p] E := AlgHom.card ℚ_[p] E 𝕃
  have hle : Fintype.card (B →ₐ[ℤ_[p]] 𝕃) ≤ d := by
    have h := (linearIndependent_fτ ℤ_[p] B 𝕃).fintype_card_le_finrank
    rwa [Subspace.dual_finrank_eq, Module.finrank_baseChange] at h
  have hge : d ≤ Fintype.card (B →ₐ[ℤ_[p]] 𝕃) :=
    hdE.trans (hcardE ▸ Fintype.card_le_of_injective res hres)
  have hcard : Fintype.card (B →ₐ[ℤ_[p]] 𝕃) = d := le_antisymm hle hge
  refine ⟨hcard, ?_⟩

  have hres_bij : Function.Bijective res := by
    rw [Fintype.bijective_iff_injective_and_card]
    have h1 : Fintype.card (E →ₐ[ℚ_[p]] 𝕃) ≤ Fintype.card (B →ₐ[ℤ_[p]] 𝕃) := Fintype.card_le_of_injective res hres
    have h2 : Fintype.card (B →ₐ[ℤ_[p]] 𝕃) ≤ Fintype.card (E →ₐ[ℚ_[p]] 𝕃) := by rw [hcard, hcardE]; exact hdE
    exact ⟨hres, le_antisymm h1 h2⟩
  intro τ
  obtain ⟨χ, rfl⟩ := hres_bij.2 τ
  let σ' : 𝕃 →ₐ[ℚ_[p]] 𝕃 := AlgHom.liftNormal χ 𝕃
  have hσ' : ∀ x : E, σ' (x : 𝕃) = χ x := fun x => AlgHom.liftNormal_commutes χ 𝕃 x
  refine ⟨AlgEquiv.ofBijective σ' (Algebra.IsAlgebraic.algHom_bijective σ'), fun b => ?_⟩
  show σ' (τ₀ p B b) = χ (τE b)
  rw [← hτE, hσ']

end S17Ind
p2m_reactivate "P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic.S17Ind"

namespace S17Ind

open scoped TensorProduct
open WithConv

theorem isUnit_point {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {T : Type*} [CommRing T] [Algebra K T] (f : WithConv (A →ₐ[K] T)) : IsUnit f := by
  obtain ⟨g, -, hl, hr⟩ := HopfAlgebra.exists_comp_antipode_convMul_eq_one (WithConv.ofConv f)
  exact ⟨⟨f, WithConv.toConv g, by simpa using hr, by simpa using hl⟩, rfl⟩

theorem map_one_of_map_mul {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {T : Type*} [CommRing T] [Algebra K T] {X : Type*} [MulOneClass X]
    (e : X → WithConv (A →ₐ[K] T)) (he : ∀ x y, e (x * y) = e x * e y) : e 1 = 1 := by
  have h : e 1 * e 1 = e 1 * 1 := by rw [← he, one_mul, mul_one]
  exact (isUnit_point (e 1)).mul_left_cancel h

variable (p : ℕ) [Fact p.Prime]
variable (B : Type) [CommRing B] [Algebra ℤ_[p] B]

local notation "𝕃" => AlgebraicClosure ℚ_[p]

noncomputable def mτ {T : Type} [CommRing T] [Algebra ℤ_[p] T] (τ : B →ₐ[ℤ_[p]] T) : B ⊗[ℤ_[p]] T →ₐ[ℤ_[p]] T :=
  Algebra.TensorProduct.lift τ (AlgHom.id ℤ_[p] T) (fun _ _ => Commute.all _ _)

@[scoped simp] theorem mτ_tmul {T : Type} [CommRing T] [Algebra ℤ_[p] T] (τ : B →ₐ[ℤ_[p]] T) (b : B) (x : T) :
    mτ p B τ (b ⊗ₜ x) = τ b * x := by
  simp [mτ, Algebra.TensorProduct.lift_tmul]

theorem Θ_comm_apply {T : Type} [Field T] [Algebra ℤ_[p] T] (y : B ⊗[ℤ_[p]] T) (τ : B →ₐ[ℤ_[p]] T) :
    Θ ℤ_[p] B T (Algebra.TensorProduct.comm ℤ_[p] B T y) τ = mτ p B τ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [Algebra.TensorProduct.comm_tmul, Θ_tmul, mτ_tmul, mul_comm]
  | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]

theorem eq_of_forall_mτ_eq {T : Type} [Field T] [Algebra ℤ_[p] T] (hΘ : Function.Injective (Θ ℤ_[p] B T))
    {y y' : B ⊗[ℤ_[p]] T} (h : ∀ τ : B →ₐ[ℤ_[p]] T, mτ p B τ y = mτ p B τ y') : y = y' := by
  apply (Algebra.TensorProduct.comm ℤ_[p] B T).injective
  apply hΘ
  funext τ
  rw [Θ_comm_apply, Θ_comm_apply, h]

variable [Algebra B (AlgebraicClosure ℚ_[p])] [IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])]

noncomputable def mB : B ⊗[ℤ_[p]] 𝕃 →ₐ[B] 𝕃 :=
  Algebra.TensorProduct.lift (Algebra.ofId B 𝕃) (AlgHom.id ℤ_[p] 𝕃) (fun _ _ => Commute.all _ _)

theorem mB_apply (y : B ⊗[ℤ_[p]] 𝕃) : mB p B y = mτ p B (τ₀ p B) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [mτ_tmul]; simp [mB, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

noncomputable abbrev galZ (σ : 𝕃 ≃ₐ[ℚ_[p]] 𝕃) : 𝕃 →ₐ[ℤ_[p]] 𝕃 := (σ.restrictScalars ℤ_[p]).toAlgHom

theorem mB_map_galZ (σ : 𝕃 ≃ₐ[ℚ_[p]] 𝕃) (y : B ⊗[ℤ_[p]] 𝕃) :
    mB p B (Algebra.TensorProduct.map (AlgHom.id B B) (galZ p σ) y) =
      σ (mτ p B ((galZ p σ.symm).comp (τ₀ p B)) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mB_apply, mτ_tmul, mτ_tmul, map_mul]
    show τ₀ p B b * σ x = σ (σ.symm (τ₀ p B b)) * σ x
    rw [AlgEquiv.apply_symm_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

end S17Ind
p2m_reactivate "P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic.S17Ind"

open S17Ind WithConv in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℤ_[p] B] [Module.Finite ℤ_[p] B] [Module.Free ℤ_[p] B]
    [Algebra.Etale ℤ_[p] B]
    [Algebra B (AlgebraicClosure ℚ_[p])] [IsScalarTower ℤ_[p] B (AlgebraicClosure ℚ_[p])]
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Finite B H] [Module.Free B H] [Coalgebra.IsCocomm B H]
    (W : Type) [CommRing W] [HopfAlgebra ℤ_[p] W]
    (e : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T],
      WithConv (W →ₐ[ℤ_[p]] T) ≃ WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] T)))
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ_[p] T] (f g : WithConv (W →ₐ[ℤ_[p]] T)),
      e T (f * g) = e T f * e T g)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ_[p] T] [CommRing T'] [Algebra ℤ_[p] T'] (u : T →ₐ[ℤ_[p]] T')
      (f : WithConv (W →ₐ[ℤ_[p]] T)),
      e T' (WithConv.toConv (u.comp f.ofConv))
        = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv)) :
    ∃ (P : Type) (_ : AddCommGroup P) (_ : DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P)
      (eW : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ P)
      (π₀ : P →+ Additive (WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]))),
      (∀ f g, eW (f * g) = eW f + eW g) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (f g : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ x : W, g x = σ (f x)) → eW g = σ • (eW f)) ∧
      (∀ f : WithConv (W →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
        Additive.toMul (π₀ (eW f)) = WithConv.toConv
          ((Algebra.TensorProduct.lift (Algebra.ofId B (AlgebraicClosure ℚ_[p])) (AlgHom.id ℤ_[p] (AlgebraicClosure ℚ_[p]))
            (fun _ _ => Commute.all _ _)).comp (e (AlgebraicClosure ℚ_[p]) f).ofConv)) ∧
      (∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]), (∀ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b) →
        ∀ (x : P) (g : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p])),
          (∀ h : H, g h = σ (Additive.toMul (π₀ x) h)) → π₀ (σ • x) = Additive.ofMul g) ∧
      (∀ x : P, (∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], π₀ (σ • x) = 0) → x = 0) ∧
      (∀ f : WithConv (H →ₐ[B] AlgebraicClosure ℚ_[p]), ∃ x : P, π₀ x = Additive.ofMul f ∧
        ∀ σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], (∃ b : B, σ (algebraMap B (AlgebraicClosure ℚ_[p]) b) ≠ algebraMap B (AlgebraicClosure ℚ_[p]) b) →
          π₀ (σ • x) = 0) := by
  classical

  obtain ⟨instF, hcard, htrans⟩ := card_algHom_and_transitive p B
  have hΘ : Function.Bijective (Θ ℤ_[p] B (AlgebraicClosure ℚ_[p])) := Θ_bijective ℤ_[p] B (AlgebraicClosure ℚ_[p]) hcard

  have hunit : ∀ f : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])), IsUnit f := fun f => isUnit_point f

  have hcommW : ∀ f g : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])), f * g = g * f := fun f g =>
    (e (AlgebraicClosure ℚ_[p])).injective (by
      rw [he_mul, he_mul]
      exact mul_comm (e (AlgebraicClosure ℚ_[p]) f) (e (AlgebraicClosure ℚ_[p]) g))
  letI instCW : CommMonoid (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) :=
    { (inferInstance : Monoid (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))) with mul_comm := hcommW }
  let P : Type := Additive (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))ˣ
  let eW : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) ≃ P :=
    { toFun := fun f => Additive.ofMul (hunit f).unit
      invFun := fun m => ((Additive.toMul m : (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))ˣ) : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))
      left_inv := fun f => IsUnit.unit_spec (hunit f)
      right_inv := fun m => by
        apply Additive.toMul.injective
        exact Units.ext (IsUnit.unit_spec (hunit _)) }
  have heW_symm : ∀ m : P, eW.symm m = ((Additive.toMul m : (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))ˣ) : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) := fun _ => rfl
  have he : ∀ f g, eW (f * g) = eW f + eW g := by
    intro f g
    apply Additive.toMul.injective
    apply Units.ext
    show ((hunit (f * g)).unit : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) = ((hunit f).unit * (hunit g).unit : (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))ˣ)
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
  have he_symm : ∀ m m' : P, eW.symm (m + m') = eW.symm m * eW.symm m' := by
    intro m m'
    apply eW.injective
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have heW_one : eW 1 = 0 := by
    apply Additive.toMul.injective
    exact Units.ext (IsUnit.unit_spec (hunit 1))
  have heW_symm_zero : eW.symm 0 = 1 := by rw [← heW_one, Equiv.symm_apply_apply]

  let gal : ((AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p])) → WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) → WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) := fun σ f =>
    WithConv.toConv ((galZ p σ).comp (WithConv.ofConv f))
  have hgal_apply : ∀ σ f (w : W), gal σ f w = σ (f w) := fun _ _ _ => rfl
  have hgal_one : ∀ f, gal 1 f = f := fun f => by apply WithConv.ext; apply AlgHom.ext; intro w; rfl
  have hgal_mul : ∀ σ σ' f, gal (σ * σ') f = gal σ (gal σ' f) := fun _ _ _ => by
    apply WithConv.ext; apply AlgHom.ext; intro w; rfl
  have hgal_convMul : ∀ σ f g, gal σ (f * g) = gal σ f * gal σ g := by
    intro σ f g
    apply WithConv.ext
    show (galZ p σ).comp (f * g).ofConv = (WithConv.toConv ((galZ p σ).comp f.ofConv) * WithConv.toConv ((galZ p σ).comp g.ofConv)).ofConv
    rw [AlgHom.comp_convMul_distrib]
  have hgal_unit : ∀ σ, gal σ 1 = 1 := by
    intro σ
    apply WithConv.ext; apply AlgHom.ext; intro w
    rw [hgal_apply]
    show σ ((1 : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) w) = (1 : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) w
    rw [AlgHom.convOne_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]), AlgEquiv.commutes]
  letI instP : DistribMulAction ((AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p])) P :=
    { smul := fun σ m => eW (gal σ (eW.symm m))
      one_smul := fun m => by
        show eW (gal 1 (eW.symm m)) = m
        rw [hgal_one, Equiv.apply_symm_apply]
      mul_smul := fun σ σ' m => by
        show eW (gal (σ * σ') (eW.symm m)) = eW (gal σ (eW.symm (eW (gal σ' (eW.symm m)))))
        rw [hgal_mul, Equiv.symm_apply_apply]
      smul_zero := fun σ => by
        show eW (gal σ (eW.symm 0)) = 0
        rw [heW_symm_zero, hgal_unit, heW_one]
      smul_add := fun σ m m' => by
        show eW (gal σ (eW.symm (m + m'))) = eW (gal σ (eW.symm m)) + eW (gal σ (eW.symm m'))
        rw [he_symm, hgal_convMul, he] }
  have hsmul : ∀ (σ : (AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p])) (m : P), σ • m = eW (gal σ (eW.symm m)) := fun _ _ => rfl

  have heL_one : e (AlgebraicClosure ℚ_[p]) 1 = 1 := map_one_of_map_mul (e (AlgebraicClosure ℚ_[p])) (he_mul (AlgebraicClosure ℚ_[p]))

  have hone_L : ∀ h : H, (1 : WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p]))) h = algebraMap B (AlgebraicClosure ℚ_[p]) (Coalgebra.counit h) := fun h =>
    AlgHom.convOne_apply h
  have hone_BL : ∀ h : H, (1 : WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])))) h = (Coalgebra.counit (R := B) h) ⊗ₜ (1 : (AlgebraicClosure ℚ_[p])) :=
    fun h => AlgHom.convOne_apply h
  let comp : WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) → WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p])) := fun G =>
    WithConv.toConv ((mB p B).comp G.ofConv)
  have hcomp_mul : ∀ G G', comp (G * G') = comp G * comp G' := by
    intro G G'
    apply WithConv.ext
    show (mB p B).comp (G * G').ofConv = _
    rw [AlgHom.comp_convMul_distrib]
  have hcomp_one : comp 1 = 1 := by
    apply WithConv.ext; apply AlgHom.ext; intro h
    show mB p B ((1 : WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])))) h) = (1 : WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p]))) h
    rw [hone_BL, hone_L, mB_apply, mτ_tmul, mul_one]
    rfl
  let π₀ : P →+ Additive (WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p]))) :=
    { toFun := fun m => Additive.ofMul (comp (e (AlgebraicClosure ℚ_[p]) (eW.symm m)))
      map_zero' := by
        apply Additive.toMul.injective
        show comp (e (AlgebraicClosure ℚ_[p]) (eW.symm 0)) = 1
        rw [heW_symm_zero, heL_one, hcomp_one]
      map_add' := fun m m' => by
        apply Additive.toMul.injective
        show comp (e (AlgebraicClosure ℚ_[p]) (eW.symm (m + m'))) = comp (e (AlgebraicClosure ℚ_[p]) (eW.symm m)) * comp (e (AlgebraicClosure ℚ_[p]) (eW.symm m'))
        rw [he_symm, he_mul, hcomp_mul] }
  have hπ₀ : ∀ m : P, Additive.toMul (π₀ m) = comp (e (AlgebraicClosure ℚ_[p]) (eW.symm m)) := fun _ => rfl
  have hπ₀_apply : ∀ (m : P) (h : H), (Additive.toMul (π₀ m)).ofConv h = mB p B ((e (AlgebraicClosure ℚ_[p]) (eW.symm m)).ofConv h) :=
    fun _ _ => rfl

  have he_gal : ∀ (σ : (AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p])) (f : WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]))) (h : H),
      (e (AlgebraicClosure ℚ_[p]) (gal σ f)).ofConv h = Algebra.TensorProduct.map (AlgHom.id B B) (galZ p σ) ((e (AlgebraicClosure ℚ_[p]) f).ofConv h) := by
    intro σ f h
    have := he_nat (AlgebraicClosure ℚ_[p]) (AlgebraicClosure ℚ_[p]) (galZ p σ) f
    rw [show gal σ f = WithConv.toConv ((galZ p σ).comp f.ofConv) from rfl, this]
    rfl

  refine ⟨P, inferInstanceAs (AddCommGroup (Additive (WithConv (W →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])))ˣ)), instP, eW, π₀, he, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ f g hfg
    rw [hsmul, Equiv.symm_apply_apply]
    congr 1
    apply WithConv.ext; apply AlgHom.ext; intro w
    exact hfg w
  ·
    intro f
    rw [hπ₀, Equiv.symm_apply_apply]
    rfl
  ·
    intro σ hσ x g hg
    apply Additive.toMul.injective
    rw [hπ₀]
    show comp (e (AlgebraicClosure ℚ_[p]) (eW.symm (σ • x))) = g
    apply WithConv.ext; apply AlgHom.ext; intro h
    show mB p B ((e (AlgebraicClosure ℚ_[p]) (eW.symm (σ • x))).ofConv h) = g h
    have hfix : (galZ p σ.symm).comp (τ₀ p B) = τ₀ p B := AlgHom.ext fun b => by
      show σ.symm (algebraMap B (AlgebraicClosure ℚ_[p]) b) = algebraMap B (AlgebraicClosure ℚ_[p]) b
      rw [← hσ b, AlgEquiv.symm_apply_apply, hσ b]
    rw [hg h, hsmul, Equiv.symm_apply_apply, he_gal, mB_map_galZ, hπ₀_apply, mB_apply, hfix]
  ·
    intro x hx
    have key : ∀ τ : B →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p]), ∀ h : H,
        mτ p B τ ((e (AlgebraicClosure ℚ_[p]) (eW.symm x)).ofConv h) = mτ p B τ ((1 : WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])))) h) := by
      intro τ h
      obtain ⟨σ', hσ'⟩ := htrans τ

      have h0 := hx σ'.symm
      have h1 : mB p B ((e (AlgebraicClosure ℚ_[p]) (eW.symm (σ'.symm • x))).ofConv h) = algebraMap B (AlgebraicClosure ℚ_[p]) (Coalgebra.counit h) := by
        rw [← hone_L h, ← hπ₀_apply, h0]
        rfl
      rw [hsmul, Equiv.symm_apply_apply, he_gal, mB_map_galZ, AlgEquiv.symm_symm] at h1
      have hτ : (galZ p σ').comp (τ₀ p B) = τ := AlgHom.ext fun b => hσ' b
      rw [hτ] at h1
      have h2 : mτ p B τ ((e (AlgebraicClosure ℚ_[p]) (eW.symm x)).ofConv h) = σ' (algebraMap B (AlgebraicClosure ℚ_[p]) (Coalgebra.counit h)) := by
        rw [← h1, AlgEquiv.apply_symm_apply]
      rw [h2, hone_BL, mτ_tmul, mul_one, ← hσ']
    have hG : (e (AlgebraicClosure ℚ_[p]) (eW.symm x)).ofConv = (1 : WithConv (H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])))).ofConv := by
      apply AlgHom.ext
      intro h
      exact eq_of_forall_mτ_eq p B hΘ.1 (fun τ => key τ h)
    have hG' : e (AlgebraicClosure ℚ_[p]) (eW.symm x) = 1 := WithConv.ext hG
    rw [← heL_one] at hG'
    have hf : eW.symm x = 1 := (e (AlgebraicClosure ℚ_[p])).injective hG'
    rw [← Equiv.apply_symm_apply eW x, hf, heW_one]
    try rfl
  ·
    intro f
    let Rfun : H → ((B →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) → (AlgebraicClosure ℚ_[p])) := fun h τ =>
      if τ = τ₀ p B then f h else τ (Coalgebra.counit (R := B) h)
    let Rhom : H →+* ((B →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) → (AlgebraicClosure ℚ_[p])) :=
      { toFun := Rfun
        map_one' := by funext τ; simp only [Rfun]; split_ifs <;> simp
        map_mul' := fun x y => by funext τ; simp only [Rfun, Pi.mul_apply]; split_ifs <;> simp
        map_zero' := by funext τ; simp only [Rfun]; split_ifs <;> simp
        map_add' := fun x y => by funext τ; simp only [Rfun, Pi.add_apply]; split_ifs <;> simp }
    have hRhom : ∀ h τ, Rhom h τ = Rfun h τ := fun _ _ => rfl
    let ΘE : ((AlgebraicClosure ℚ_[p]) ⊗[ℤ_[p]] B) ≃+* ((B →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])) → (AlgebraicClosure ℚ_[p])) := RingEquiv.ofBijective (Θ ℤ_[p] B (AlgebraicClosure ℚ_[p])) hΘ
    let G0 : H →+* B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p]) :=
      ((Algebra.TensorProduct.comm ℤ_[p] (AlgebraicClosure ℚ_[p]) B).toRingEquiv.toRingHom.comp ΘE.symm.toRingHom).comp Rhom
    have hG0 : ∀ h τ, mτ p B τ (G0 h) = Rfun h τ := by
      intro h τ
      rw [← Θ_comm_apply]
      show Θ ℤ_[p] B (AlgebraicClosure ℚ_[p]) ((Algebra.TensorProduct.comm ℤ_[p] B (AlgebraicClosure ℚ_[p])) ((Algebra.TensorProduct.comm ℤ_[p] (AlgebraicClosure ℚ_[p]) B) (ΘE.symm (Rhom h)))) τ = _
      rw [show (Algebra.TensorProduct.comm ℤ_[p] B (AlgebraicClosure ℚ_[p])) ((Algebra.TensorProduct.comm ℤ_[p] (AlgebraicClosure ℚ_[p]) B) (ΘE.symm (Rhom h))) = ΘE.symm (Rhom h)
        from (Algebra.TensorProduct.comm ℤ_[p] (AlgebraicClosure ℚ_[p]) B).symm_apply_apply _]
      show ΘE (ΘE.symm (Rhom h)) τ = _
      rw [RingEquiv.apply_symm_apply]
      rfl
    have hRfun_alg : ∀ (b : B) (τ : B →ₐ[ℤ_[p]] (AlgebraicClosure ℚ_[p])), Rfun (algebraMap B H b) τ = τ b := by
      intro b τ
      simp only [Rfun]
      split_ifs with hτ
      · rw [hτ, AlgHom.commutes]; rfl
      · rw [Bialgebra.counit_algebraMap]
    have hG0_alg : ∀ b : B, G0 (algebraMap B H b) = algebraMap B (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])) b := by
      intro b
      apply eq_of_forall_mτ_eq p B hΘ.1
      intro τ
      rw [hG0, hRfun_alg, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        mτ_tmul, mul_one]
    let G : H →ₐ[B] (B ⊗[ℤ_[p]] (AlgebraicClosure ℚ_[p])) :=
      { G0 with commutes' := hG0_alg }
    have hG : ∀ h τ, mτ p B τ (G h) = Rfun h τ := hG0
    let x : P := eW ((e (AlgebraicClosure ℚ_[p])).symm (WithConv.toConv G))
    have hex : e (AlgebraicClosure ℚ_[p]) (eW.symm x) = WithConv.toConv G := by
      show e (AlgebraicClosure ℚ_[p]) (eW.symm (eW ((e (AlgebraicClosure ℚ_[p])).symm (WithConv.toConv G)))) = _
      rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    refine ⟨x, ?_, ?_⟩
    · apply Additive.toMul.injective
      rw [hπ₀, hex]
      show comp (WithConv.toConv G) = f
      apply WithConv.ext; apply AlgHom.ext; intro h
      show mB p B (G h) = f h
      rw [mB_apply, hG]
      simp only [Rfun, if_pos rfl]
    · rintro σ ⟨b₀, hb₀⟩
      apply Additive.toMul.injective
      rw [hπ₀]
      show comp (e (AlgebraicClosure ℚ_[p]) (eW.symm (σ • x))) = (1 : WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p])))
      apply WithConv.ext; apply AlgHom.ext; intro h
      show mB p B ((e (AlgebraicClosure ℚ_[p]) (eW.symm (σ • x))).ofConv h) = (1 : WithConv (H →ₐ[B] (AlgebraicClosure ℚ_[p]))) h
      rw [hsmul, Equiv.symm_apply_apply, he_gal, hex, mB_map_galZ, hone_L]
      show σ (mτ p B ((galZ p σ.symm).comp (τ₀ p B)) (G h)) = _
      rw [hG]
      have hne : (galZ p σ.symm).comp (τ₀ p B) ≠ τ₀ p B := by
        intro heq
        apply hb₀
        have := AlgHom.congr_fun heq b₀
        change σ.symm (algebraMap B (AlgebraicClosure ℚ_[p]) b₀) = algebraMap B (AlgebraicClosure ℚ_[p]) b₀ at this
        rw [← this, AlgEquiv.apply_symm_apply, this]
      simp only [Rfun, if_neg hne]
      show σ (σ.symm (τ₀ p B (Coalgebra.counit h))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl

end S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic
end P2MW
export P2MW.S_HopfAlgebra_exists_distribMulAction_withConv_equiv_of_weilRestriction_points_padic (solution)
