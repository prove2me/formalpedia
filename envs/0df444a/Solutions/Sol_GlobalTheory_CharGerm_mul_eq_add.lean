-- Prove2me | solution 1 for GlobalTheory.CharGerm.mul_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:18:23.736795+00:00
-- url     : https://prove2.me/submissions/a3752f30-f002-4d54-8448-1405e726211c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_CharGerm_exists_linear
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
include h0 hnat hinj hsurj
namespace GlobalTheory.CharGerm
theorem _root_.solution {S : Type} [CommRing S] [Algebra R₀ S] {I : Ideal S} (hI : I ^ 2 = ⊥)
    {a b : Fin g → S} (ha : ∀ i, a i ∈ I) (hb : ∀ i, b i ∈ I) :
    x S a * x S b = x S (a + b) := by
  obtain ⟨d, hd⟩ := exists_linear h0 hnat hsurj
  have hmul : ∀ u ∈ I, ∀ v ∈ I, u * v = 0 := fun u hu v hv => by
    have := Ideal.mul_mem_mul hu hv
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have hnil : ∀ u ∈ I, IsNilpotent u := fun u hu => ⟨2, by rw [pow_two, hmul u hu u hu]⟩
  have key : ∀ u v : Fin g → S, (∀ i, u i ∈ I) → (∀ i, v i ∈ I) → x S u * x S v =
      x S (fun i => ∑ k, d i (Sum.inl k) • u k + ∑ k, d i (Sum.inr k) • v k) := by
    intro u v hu hv
    have hm : ∀ k, Sum.elim u v k ∈ I := by
      rintro (k | k)
      exacts [hu k, hv k]
    have := hd S (Sum.elim u v) (fun k l => hmul _ (hm k) _ (hm l))
    simpa only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type] using this
  have hsum : ∀ (r : Fin g → R₀) (u : Fin g → S), (∀ i, u i ∈ I) → ∑ k, r k • u k ∈ I :=
    fun r u hu => Ideal.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (hu k)
  have h1 := key a 0 ha (fun _ => zero_mem _)
  have h2 := key 0 b (fun _ => zero_mem _) hb
  simp only [h0, _root_.mul_one, _root_.one_mul, Pi.zero_apply, smul_zero, Finset.sum_const_zero,
    add_zero, zero_add] at h1 h2
  have h1' := hinj S _ _ (fun i => hnil _ (ha i)) (fun i => hnil _ (hsum _ _ ha)) h1
  have h2' := hinj S _ _ (fun i => hnil _ (hb i)) (fun i => hnil _ (hsum _ _ hb)) h2
  rw [key a b ha hb]
  congr 1
  funext i
  rw [Pi.add_apply, congrFun h1' i, congrFun h2' i]
end GlobalTheory.CharGerm
