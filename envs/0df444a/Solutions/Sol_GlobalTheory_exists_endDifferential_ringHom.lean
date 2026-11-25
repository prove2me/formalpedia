-- Prove2me | solution 1 for GlobalTheory.exists_endDifferential_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:44:30.458392+00:00
-- url     : https://prove2.me/submissions/9dd947bf-802e-4659-b611-69fb88913bac

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
variable {R₀ : Type} [CommRing R₀]
private lemma endDiff_exists_lift {O R : LAlg R₀} (s : LHom O R) (i : (R : Type)) (hi : i * i = 0) :
    ∃ φ : LHom (DualNum.dualPair O).D R, φ.comp (DualNum.dualPair O).σ = s ∧
      φ.1 (DualNum.dualPair O).η = i := by
  let ψ : DualNum.DN O →ₐ[R₀] (R : Type) :=
    Ideal.Quotient.liftₐ _ (Polynomial.aevalTower s.1 i) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [pow_two, hi])
  have hσ : ∀ r, ψ ((DualNum.dualPair O).σ.1 r) = s.1 r := fun r => by
    change ψ (algebraMap (O : Type) (DualNum.DN O) r) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
    exact Polynomial.aevalTower_C s.1 i r
  have hη : ψ (DualNum.dualPair O).η = i := by
    change ψ (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aevalTower_X s.1 i
  refine ⟨⟨ψ, ⟨fun d hd => ?_⟩⟩, ?_, hη⟩
  · have hk : d - (DualNum.dualPair O).σ.1 ((DualNum.dualPair O).π.1 d) ∈
        RingHom.ker (DualNum.dualPair O).π.1 := by
      rw [RingHom.mem_ker, map_sub, (DualNum.dualPair O).sect, sub_self]
    rw [(DualNum.dualPair O).ker_eq] at hk
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hk
    have h1 : ψ y * i = ψ d - s.1 ((DualNum.dualPair O).π.1 d) := by
      rw [← hσ, ← hη]
      exact (map_mul ψ _ _).symm.trans ((congrArg ψ hy).trans (map_sub ψ _ _))
    have hn : IsNilpotent (-(ψ y * i)) := ⟨2, by
      rw [show (-(ψ y * i)) ^ 2 = ψ y * ψ y * (i * i) by ring, hi, mul_zero]⟩
    have hu : IsUnit (s.1 ((DualNum.dualPair O).π.1 d)) := by
      have h2 := hn.isUnit_add_left_of_commute (u := ψ d) hd (Commute.all _ _)
      rw [h1] at h2
      simpa using h2
    exact (DualNum.dualPair O).π.2.map_nonunit d (s.2.map_nonunit _ hu)
  · exact Subtype.ext (AlgHom.ext hσ)
private lemma endDiff_ηmap_surj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Surjective Dp.ηmap := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [Submodule.restrictScalars_mem, Dp.ker_eq] at hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  have hk : y - Dp.σ.1 (Dp.π.1 y) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq] at hk
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨Dp.π.1 y, Subtype.ext ?_⟩
  change Dp.σ.1 (Dp.π.1 y) * Dp.η = y * Dp.η
  have := Dp.η_sq
  linear_combination (-Dp.η) * (-hz) - z * this
private lemma endDiff_ηmap_inj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Injective Dp.ηmap := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  exact Dp.free r (congrArg Subtype.val hr)
private lemma endDiff_coord {g : ℕ} {V M : Type} [AddCommGroup V] [Module R₀ V] [AddCommGroup M]
    [Module R₀ M] (gb : Module.Basis (Fin g) R₀ V) :
    Function.Bijective (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) := by
  have : (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft gb).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  rw [this]
  exact (TensorProduct.equivFinsuppOfBasisLeft gb).symm.bijective.comp
    Finsupp.equivFunOnFinite.symm.bijective
private lemma endDiff_exists {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) : ∃ d, endDiff_IsMat gb e d := by
  let Dp := DualNum.dualPair O
  have h1 : ∀ l, ∃ c : Fin g → (O : Type), e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c k)) := fun l => by
    have h0 : B.map Dp.π (e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk))) = 0 := by
      rw [← e.nat, (B.tg_ker Dp.π Dp.sqZero _).2 ⟨_, rfl⟩, map_zero]
    obtain ⟨v, hv⟩ := (B.tg_ker Dp.π Dp.sqZero _).1 h0
    obtain ⟨m, rfl⟩ := (endDiff_coord (M := Dp.π.ker) gb).2 v
    choose c hc using fun k => endDiff_ηmap_surj Dp (m k)
    exact ⟨c, by rw [← hv]; simp only [hc]⟩
  choose c hc using h1
  refine ⟨fun k l => c l k, ?_⟩
  intro R S s π hπ l i m hm
  have hi : (i : (R : Type)) * i = 0 := by
    have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
    rw [hπ.2] at this
    simpa using this
  obtain ⟨φ, hφ, hη⟩ := endDiff_exists_lift s (i : (R : Type)) hi
  have hs : ∀ r, φ.1 (Dp.σ.1 r) = s.1 r := fun r => by rw [← hφ]; rfl
  have hf : ∀ a ∈ Dp.π.ker, φ.1.toLinearMap a ∈ π.ker := fun a ha => by
    obtain ⟨r, hr⟩ := endDiff_ηmap_surj Dp ⟨a, ha⟩
    have : a = Dp.σ.1 r * Dp.η := (congrArg Subtype.val hr).symm
    rw [this]
    change φ.1 (Dp.σ.1 r * Dp.η) ∈ RingHom.ker π.1
    rw [map_mul, hη]
    exact Ideal.mul_mem_left _ _ i.2
  have hA : gb l ⊗ₜ[R₀] i = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (gb l ⊗ₜ[R₀] Dp.ηk) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext hη.symm
  have hB : ∑ k, gb k ⊗ₜ[R₀] m k = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c l k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext ?_
    change _ = φ.1 (Dp.σ.1 (c l k) * Dp.η)
    rw [hm k, map_mul, hη, hs]
  rw [hA, hB, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, ← hc l,
    ← e.nat, hφ]
private lemma endDiff_spec {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (l : Fin g) (r : (O : Type)) :
    e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap r)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d k l * r)) :=
  h Dp.σ Dp.π Dp.sqZero l _ _ fun k => by
    change Dp.σ.1 (d k l * r) * Dp.η = Dp.σ.1 (d k l) * (Dp.σ.1 r * Dp.η)
    rw [map_mul, _root_.mul_assoc]
private lemma endDiff_unique {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (d' : Matrix (Fin g) (Fin g) (O : Type))
    (h' : ∀ l, e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap 1)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d' k l))) : d = d' := by
  ext k l
  have h1 := B.tg_inj _ _ ((endDiff_spec h Dp l 1).symm.trans (h' l))
  have h2 := (endDiff_coord (M := Dp.π.ker) gb).1 h1
  simpa using endDiff_ηmap_inj Dp (congrFun h2 k)
end GlobalTheory
end
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O),
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    ∃ dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type), (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ g B O gb O₀ _ f hf
  choose d hd using fun a => endDiff_exists gb (f a)
  let Dp := DualNum.dualPair O
  have hadd : ∀ a b, d (a + b) = d a + d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).1, endDiff_spec (hd a), endDiff_spec (hd b), ← map_add,
        ← Finset.sum_add_distrib]
      simp [TensorProduct.tmul_add]
  have hone : d 1 = 1 :=
    endDiff_unique (hd _) Dp _ fun l => by
      rw [(hf _ _).1, Finset.sum_eq_single l]
      · simp
      · intro k _ hk
        simp [Matrix.one_apply_ne hk]
      · simp
  have hmul : ∀ a b, d (a * b) = d a * d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).2, endDiff_spec (hd b), map_sum, map_sum]
      simp only [endDiff_spec (hd a)]
      rw [← map_sum, Finset.sum_comm]
      simp [Matrix.mul_apply, TensorProduct.tmul_sum]
  have hzero : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  exact ⟨⟨⟨⟨d, hone⟩, hmul⟩, hzero, hadd⟩, fun a => hd a⟩
end GlobalTheory
