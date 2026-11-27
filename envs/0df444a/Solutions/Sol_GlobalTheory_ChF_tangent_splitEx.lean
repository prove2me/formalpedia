-- Prove2me | solution 1 for GlobalTheory.ChF.tangent_splitEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:50.436431+00:00
-- url     : https://prove2.me/submissions/41b04d82-d343-4ad2-afbb-a7bd5a25d105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqSplitExact
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
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
private theorem isUnit_of_map_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (h : M.map (Ideal.Quotient.mk I) = 1) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h, Matrix.det_one, map_one]
  have h2 := IsAdicComplete.le_jacobson_bot I (Ideal.Quotient.eq.1 h1)
  have := Ideal.mem_jacobson_bot.1 h2 1
  simpa using this
private theorem splitEx_of_exact {K : Type} [CommRing K] {d r g : ℕ} (A : Matrix (Fin d) (Fin r) K)
    (B : Matrix (Fin g) (Fin d) K) (h0 : B * A = 0) (h1 : ∀ w, ∃ v, B *ᵥ v = w)
    (h2 : ∀ v, B *ᵥ v = 0 → ∃ t, A *ᵥ t = v) (h3 : ∀ t, A *ᵥ t = 0 → t = 0) : SplitEx A B := by
  choose v hv using h1
  let B' : Matrix (Fin d) (Fin g) K := Matrix.of fun i j => v (Pi.single j 1) i
  have hB : B * B' = 1 := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.one_apply, ← Pi.single_apply j (1 : K) i, ← this]
    rfl
  have h4 : ∀ j : Fin d, ∃ t, A *ᵥ t = (1 - B' * B) *ᵥ (Pi.single j 1) := fun j => h2 _ (by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hB, Matrix.mul_one, Matrix.one_mul, sub_self,
      Matrix.zero_mulVec])
  choose t ht using h4
  let A' : Matrix (Fin r) (Fin d) K := Matrix.of fun i j => t j i
  have hA : A * A' = 1 - B' * B := by
    ext i j
    have := congrFun (ht j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  refine ⟨h0, A', B', ?_, hB, by rw [hA]; simp⟩
  have h5 : A * (A' * A - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hA, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp
  rw [← sub_eq_zero]
  ext i j
  have := h3 ((A' * A - 1) *ᵥ Pi.single j 1) (by rw [Matrix.mulVec_mulVec, h5, Matrix.zero_mulVec])
  rw [Matrix.mulVec_single_one] at this
  exact congrFun this i
private theorem splitEx_lift {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {d r g : ℕ}
    (A : Matrix (Fin d) (Fin r) R) (B : Matrix (Fin g) (Fin d) R) (h0 : B * A = 0)
    (h : SplitEx (A.map (Ideal.Quotient.mk I)) (B.map (Ideal.Quotient.mk I))) : SplitEx A B := by
  obtain ⟨-, A1, B1, h1, h2, h3⟩ := h
  let A0 : Matrix (Fin r) (Fin d) R := A1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  let B0 : Matrix (Fin d) (Fin g) R := B1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  have hA0 : A0.map (Ideal.Quotient.mk I) = A1 := by
    ext i j; exact Function.surjInv_eq _ _
  have hB0 : B0.map (Ideal.Quotient.mk I) = B1 := by
    ext i j; exact Function.surjInv_eq _ _
  obtain ⟨U, hU⟩ := isUnit_of_map_eq_one I (A0 * A) (by rw [Matrix.map_mul, hA0, h1])
  obtain ⟨V, hV⟩ := isUnit_of_map_eq_one I (B * B0) (by rw [Matrix.map_mul, hB0, h2])
  obtain ⟨M, hM⟩ := isUnit_of_map_eq_one I (A * A0 + B0 * B) (by
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hA0, hB0, h3])
  obtain ⟨B', hB', hB0'⟩ : ∃ B' : Matrix (Fin d) (Fin g) R, B * B' = 1 ∧ B0 = B' * V.val :=
    ⟨B0 * (V⁻¹).val, by rw [← Matrix.mul_assoc, ← hV]; simp, by rw [Matrix.mul_assoc]; simp⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : Matrix (Fin r) (Fin d) R, A2 * A = 1 :=
    ⟨(U⁻¹).val * A0, by rw [Matrix.mul_assoc, ← hU]; simp⟩
  have e1 : A2 * (1 - B' * B) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp [hA2]
  have e2 : A2 * (1 - B' * B) * B' = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, hB']; simp
  refine ⟨h0, A2 * (1 - B' * B), B', e1, hB', ?_⟩
  generalize A2 * (1 - B' * B) = A' at e1 e2
  have p1 : (A * A' + B' * B) * A = A := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e1, h0]; simp
  have p2 : (A * A' + B' * B) * B' = B' := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, hB']; simp
  have p3 : (A * A' + B' * B) * M.val = 1 * M.val := by
    rw [hM, hB0', Matrix.mul_add, ← Matrix.mul_assoc, p1, Matrix.mul_assoc B', ← Matrix.mul_assoc _ B', p2,
      Matrix.one_mul]
  exact (Units.mul_left_inj M).1 p3
section Dual
variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K]
private theorem epsV_nil {n : ℕ} (v : Fin n → K) (i : Fin n) : IsNilpotent (epsV v i) :=
  ⟨2, by rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩
private theorem epsV_zero {n : ℕ} : epsV (0 : Fin n → K) = 0 := by
  funext i; exact TrivSqZeroExt.inr_zero _
private theorem epsV_inj {n : ℕ} {v w : Fin n → K} (h : epsV v = epsV w) : v = w := by
  funext i; exact TrivSqZeroExt.inr_injective (congrFun h i)
private theorem nv_epsV {n m : ℕ} (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (v : Fin n → K) : (fun j => nv (algebraMap R (DualNumber K)) (φ j) ![epsV v]) =
      epsV ((lin φ).map (algebraMap R K) *ᵥ v) := by
  funext j
  have h := (nv_calculus R (DualNumber K) (algebraMap R _) 1 n ![epsV v]
    (fun i j => by simpa using epsV_nil v j)).2.2.2.2.2
    (fun i j i' j' => by simp [epsV]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [epsV, Matrix.mulVec, dotProduct, TrivSqZeroExt.inr_sum, Matrix.map_apply, lin, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, TrivSqZeroExt.inr_smul]
  rfl
private theorem kills_dual {I : Ideal R} {k : ℕ} (h : Kills I k K) : Kills I k (DualNumber K) := fun t ht => by
  rw [TrivSqZeroExt.algebraMap_eq_inl', h t ht, TrivSqZeroExt.inl_zero]
private theorem exists_char {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X) (t : Fin r → K) :
    ∃ χ : Multiplicative X →* (DualNumber K)ˣ, ∀ j,
      (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j := by
  let u : Fin r → (DualNumber K)ˣ := fun j => (epsV_nil t j).isUnit_one_add.unit
  let f : X →ₗ[ℤ] Additive (DualNumber K)ˣ := β.constr ℤ fun j => Additive.ofMul (u j)
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, fun j => ?_⟩
  have : f (β j) = Additive.ofMul (u j) := β.constr_basis ℤ _ j
  change ((Additive.toMul (f (β j)) : (DualNumber K)ˣ) : DualNumber K) = _
  rw [this]; rfl
private theorem eq_epsV {n : ℕ} (a : Fin n → DualNumber K) (h : ∀ i, (a i).fst = 0) :
    a = epsV fun i => (a i).snd := by
  funext i; ext <;> simp [epsV, h]
end Dual
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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → SplitEx (lin J) (lin Q) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi
  have key : ∀ (K : Type) [CommRing K] [Algebra R K] (k : ℕ), Kills I k K →
      SplitEx ((lin J).map (algebraMap R K)) ((lin Q).map (algebraMap R K)) := by
    intro K _ _ k hK
    have hS : ∃ k, Kills I k (DualNumber K) := ⟨k, kills_dual hK⟩
    have hq' : ∀ v, E.q _ hS (x _ (epsV v)) = xB _ (epsV ((lin Q).map (algebraMap R K) *ᵥ v)) := fun v => by
      rw [hq _ hS _ (epsV_nil v), nv_epsV Q hQ]
    have hi' : ∀ (χ : Multiplicative X →* (DualNumber K)ˣ) t, (∀ j,
        (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j) →
        E.i _ hS χ = x _ (epsV ((lin J).map (algebraMap R K) *ᵥ t)) := fun χ t h => by
      rw [hi _ hS χ _ (epsV_nil t) h, nv_epsV J hJ]
    let ρ : DualNumber K →ₐ[R] K := TrivSqZeroExt.fstHom R K K
    let σ : K →ₐ[R] DualNumber K := TrivSqZeroExt.inlAlgHom R K K
    have hρσ : ρ.comp σ = AlgHom.id R K := by ext; rfl
    have hker : RingHom.ker ρ ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']
    have hred : ∀ {n : ℕ} (v : Fin n → K), (fun i => ρ (epsV v i)) = 0 := fun v => rfl
    refine splitEx_of_exact _ _ ?_ (fun w => ?_) (fun v hv => ?_) (fun t ht => ?_)
    · refine Matrix.ext_of_mulVec_single fun j => ?_
      obtain ⟨χ, hχ⟩ := exists_char β (Pi.single j (1 : K))
      have h1 := (E.exact _ hS _).2 ⟨χ, rfl⟩
      rw [hi' χ _ hχ, hq', ← hxB.zero, ← epsV_zero] at h1
      have h2 := epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) h1)
      rw [← Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
    · obtain ⟨z, hz, hz'⟩ := E.lift _ hS K ρ σ hρσ hker (xB _ (epsV w))
        (by rw [hxB.nat _ _ _ _ (epsV_nil w), hred, hxB.zero])
      obtain ⟨a, ha, rfl⟩ := hx.surj _ K ρ σ hρσ ⟨2, hker⟩ z hz
      rw [eq_epsV a ha, hq'] at hz'
      exact ⟨_, epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) hz')⟩
    · have h1 := hq' v
      rw [hv, epsV_zero, hxB.zero] at h1
      obtain ⟨χ, hχ⟩ := (E.exact _ hS _).1 h1
      have h2 := E.i_nat _ K ρ hS ⟨k, hK⟩ χ
      rw [hχ, hx.nat _ _ _ _ (epsV_nil v), hred, hx.zero, ← map_one (E.i K ⟨k, hK⟩)] at h2
      have h3 := E.i_inj _ _ h2
      have h4 : ∀ j, ((χ (Multiplicative.ofAdd (β j)) : DualNumber K) - 1).fst = 0 := fun j => by
        have := congrArg Units.val (DFunLike.congr_fun h3 (Multiplicative.ofAdd (β j)))
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, sub_eq_zero]
        exact this
      have h5 := hi' χ _ (fun j => (sub_eq_iff_eq_add'.1 (congrFun (eq_epsV _ h4) j)))
      rw [hχ] at h5
      exact ⟨_, (epsV_inj (hx.inj _ _ _ (epsV_nil _) (epsV_nil _) h5)).symm⟩
    · obtain ⟨χ, hχ⟩ := exists_char β t
      have h1 := hi' χ t hχ
      rw [ht, epsV_zero, hx.zero, ← map_one (E.i _ hS)] at h1
      have h2 := E.i_inj _ _ h1
      apply epsV_inj
      rw [epsV_zero]
      funext j
      have := hχ j
      rw [h2] at this
      simpa using this
  refine splitEx_lift I _ _ ?_ (key (R ⧸ I) 0 fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ht))
  ext i j
  refine IsHausdorff.haus (inferInstance : IsHausdorff I R) _ fun k => ?_
  have h1 := (key (R ⧸ I ^ (k + 1)) k fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht).1
  rw [← Matrix.map_mul] at h1
  have h2 : (lin Q * lin J) i j ∈ I ^ (k + 1) := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) h2
end GlobalTheory.ChF
