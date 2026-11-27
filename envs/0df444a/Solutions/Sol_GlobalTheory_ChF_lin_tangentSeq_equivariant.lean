-- Prove2me | solution 1 for GlobalTheory.ChF.lin_tangentSeq_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:24.374922+00:00
-- url     : https://prove2.me/submissions/34e54b73-ef4d-4259-9ca0-74387b36d0a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqEquivariant
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem tv_nil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n : ℕ}
    (v : Fin n → R) (i : Fin n) : IsNilpotent (tv e v i) :=
  ⟨2, by simp only [tv, mul_pow, pow_two e, he, mul_zero]⟩
private theorem nv_tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n m : ℕ}
    (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (v : Fin n → R) :
    (fun j => nv (algebraMap R S) (φ j) ![tv e v]) = tv e (lin φ *ᵥ v) := by
  funext j
  have h := (nv_calculus R S (algebraMap R S) 1 n ![tv e v] (fun i k => by
    fin_cases i; exact tv_nil he v k)).2.2.2.2.2 (fun i k i' k' => by
      fin_cases i; fin_cases i'
      show algebraMap R S (v k) * e * (algebraMap R S (v k') * e) = 0
      rw [_root_.mul_mul_mul_comm, he, mul_zero]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [tv, lin, Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul,
    Matrix.cons_val_fin_one, _root_.mul_assoc]
private theorem mat_ext {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin n) R)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S], (∃ k, Kills I k S) → ∀ e : S, e * e = 0 →
      ∀ v : Fin n → R, tv e (A *ᵥ v) = tv e (A' *ᵥ v)) : A = A' := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := R)) _ fun k => ?_
  have hk : Kills I k (DualNumber (R ⧸ I ^ (k + 1))) := fun t ht => by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero]
  have h1 := congrArg TrivSqZeroExt.snd (congrFun (h (DualNumber (R ⧸ I ^ (k + 1))) ⟨k, hk⟩ DualNumber.eps
    DualNumber.eps_mul_eps (Pi.single j 1)) i)
  simp only [tv, Matrix.mulVec_single_one, Matrix.col_apply,
    IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)) (DualNumber (R ⧸ I ^ (k + 1))),
    ← Algebra.smul_def, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one,
    Ideal.Quotient.algebraMap_eq] at h1
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq.1 h1)
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi f α hα
  refine ⟨fun fB αB hαB hc => mat_ext I _ _ fun S _ _ h e he v => ?_,
    fun hm hc => mat_ext I _ _ fun S _ _ h e he v => ?_⟩
  · refine hxB.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    have h1 := hc S h (x S (tv e v))
    rw [hα.2 S _ (tv_nil he v), nv_tv he α hα.1, hq S h _ (tv_nil he _), hq S h _ (tv_nil he _),
      nv_tv he Q hQ, nv_tv he Q hQ, hαB.2 S _ (tv_nil he _), nv_tv he αB hαB.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1
  · refine hx.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    let L : X →ₗ[ℤ] R := β.constr ℤ v
    have hL : ∀ j, L (β j) = v j := fun j => β.constr_basis ℤ v j
    have hL' : ∀ j, L (hm (β j)) =
        (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v) j := fun j => by
      simp [L, Module.Basis.constr_apply_fintype, Matrix.mulVec, dotProduct]
    have h1 := hc S h (chi he L.toAddMonoidHom) (chi he (L.toAddMonoidHom.comp hm)) (fun y => Units.ext rfl)
    rw [hi S h _ (tv e v) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (β j)) * e = _
        rw [hL]; rfl),
      hi S h _ (tv e (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v)) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (hm (β j))) * e = _
        rw [hL']; rfl),
      nv_tv he J hJ, nv_tv he J hJ, hα.2 S _ (tv_nil he _), nv_tv he α hα.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1
end GlobalTheory.ChF
