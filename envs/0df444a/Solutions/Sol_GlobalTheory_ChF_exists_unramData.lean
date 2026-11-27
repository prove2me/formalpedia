-- Prove2me | solution 1 for GlobalTheory.ChF.exists_unramData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:44:38.655795+00:00
-- url     : https://prove2.me/submissions/6d81dfe7-cfae-47e5-b8c2-6a21461f6e19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EmbeddingsLiftIntegersIdempotentsConjugation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicIntAlgebraOfIsAdicCompleteMatrixUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenbasisRestrictionSurjectiveEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SplittingIdempotents
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEigenIdem
import Theorems.Thm_GlobalTheory_ChF_eigB_res_surjective
import Theorems.Thm_GlobalTheory_ChF_embeddings_idempotents_conjugation
import Theorems.Thm_GlobalTheory_ChF_padicInt_algebra_of_isAdicComplete_and_matrix_unique
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_SplittingIdempotents_exists_splitting_idempotents_frobenius
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
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
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem exists_eigen_idem {O OE κ : Type} [CommRing O] [CommRing OE] [Fintype κ] [DecidableEq κ]
    {m : ℕ} (t : Fin m → (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (hε : CompleteOrthogonalIdempotents ε)
    (he : ∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = t i a • ε i) (ρ : OE →+* Matrix κ κ O) :
    ∃ e : Fin m → Matrix κ κ O, (∀ i j, e i * e j = if i = j then e i else 0) ∧ ∑ i, e i = 1 ∧
      ∀ a i, ρ a * e i = t i a • e i := by
  let Ψ : O ⊗[ℤ] OE →ₐ[O] Matrix κ κ O :=
    Algebra.TensorProduct.lift (Algebra.ofId O _) ρ.toIntAlgHom
      (fun x y => (Algebra.commutes x _ : Commute (Algebra.ofId O (Matrix κ κ O) x) (ρ.toIntAlgHom y)))
  refine ⟨fun i => Ψ (ε i), fun i j => ?_, ?_, fun a i => ?_⟩
  · rw [← map_mul]
    split_ifs with h
    · subst h; rw [(hε.idem i).eq]
    · rw [hε.ortho h, map_zero]
  · rw [← map_sum, hε.complete, map_one]
  · have h1 : Ψ (1 ⊗ₜ[ℤ] a) = ρ a := by
      refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
      rw [map_one, _root_.one_mul]
      rfl
    rw [← h1, ← map_mul, he, map_smul]
private theorem eigen_ext {p : ℕ} [Fact p.Prime] {O OE κ : Type} [CommRing O] [Algebra ℤ_[p] O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix κ κ O)
    (hρ : ∀ c : ℤ_[p], ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix κ κ O)) (t : OE →+* O)
    (e : Matrix κ κ O) (h : ∀ a, ρ (1 ⊗ₜ[ℤ] a) * e = t a • e) (x : ℤ_[p] ⊗[ℤ] OE) :
    ρ x * e = tauExt t x • e := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, add_mul, add_smul, hx, hy]
  | tmul c a =>
    have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
    have h2 : tauExt t (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * t a := by
      simp [tauExt, Algebra.ofId_apply]
    rw [h2, h1, map_mul, _root_.mul_assoc, h, hρ, smul_mul_assoc, _root_.one_mul, smul_smul]
private theorem frob_ext {p : ℕ} [Fact p.Prime] {O OE : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [CommRing OE] (hp : ¬IsUnit (p : O)) (s t : OE →+* O)
    (h : ∀ a, s a - t a ^ p ∈ IsLocalRing.maximalIdeal O) (x : ℤ_[p] ⊗[ℤ] OE) :
    tauExt s x - tauExt t x ^ p ∈ IsLocalRing.maximalIdeal O := by
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    have : IsLocalRing.residue O (p : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hp
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  have key : ∀ y z : O, y - z ^ p ∈ IsLocalRing.maximalIdeal O ↔
      IsLocalRing.residue O y = frobenius _ p (IsLocalRing.residue O z) := by
    intro y z
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, frobenius_def]
  rw [key]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    have h2 : ∀ u : OE →+* O, tauExt u (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * u a := by
      intro u
      simp [tauExt, Algebra.ofId_apply]
    have h3 := PadicInt.sub_zmodRepr_mem c
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
    obtain ⟨d, hd⟩ := h3
    have h4 : IsLocalRing.residue O (algebraMap ℤ_[p] O c) = (c.zmodRepr : IsLocalRing.ResidueField O) := by
      have : c = d * p + c.zmodRepr := by rw [hd]; ring
      conv_lhs => rw [this]
      simp [hp0]
    rw [h2, h2, map_mul, map_mul, map_mul, (key _ _).1 (h a), h4, map_natCast]
private theorem exists_eigB {O OE : Type} [CommRing O] [IsLocalRing O] [CommRing OE] {g m : ℕ}
    (t : Fin m → (OE →+* O)) (hd : ∀ i j, i ≠ j → ∃ a, IsUnit (t i a - t j a))
    (ρ : OE → Matrix (Fin g) (Fin g) O) (e : Fin m → Matrix (Fin g) (Fin g) O)
    (h1 : ∀ i j, e i * e j = if i = j then e i else 0) (h2 : ∑ i, e i = 1)
    (h3 : ∀ a i, ρ a * e i = t i a • e i) (i : Fin m) :
    ∃ (n : ℕ) (W : Fin n → Fin g → O), EigB ρ (t i) W ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (e i)) ≃ₗ[O] (Fin n → O)) := by
  set N := LinearMap.range (Matrix.mulVecLin (e i)) with hN
  have hid : ∀ w ∈ N, e i *ᵥ w = w := by
    rintro _ ⟨u, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, if_pos rfl]
  haveI : Module.Projective O N :=
    Module.Projective.of_split N.subtype (Matrix.mulVecLin (e i)).rangeRestrict
      (by ext1 w; exact Subtype.ext (hid w w.2))
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O N
  have hcomm : ∀ a j, e j * ρ a = t j a • e j := by
    intro a j
    calc e j * ρ a = e j * (ρ a * ∑ k, e k) := by rw [h2, _root_.mul_one]
      _ = ∑ k, t k a • (e j * e k) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [h3, mul_smul_comm]
      _ = t j a • e j := by
        rw [Finset.sum_eq_single j]
        · rw [h1, if_pos rfl]
        · intro k _ hk
          rw [h1, if_neg (Ne.symm hk), smul_zero]
        · simp
  refine ⟨_, fun k => (b k : Fin g → O), ⟨fun k a => ?_, fun w hw => ?_⟩, ⟨b.equivFun⟩⟩
  · have := hid _ (b k).2
    calc ρ a *ᵥ (b k : Fin g → O) = ρ a *ᵥ (e i *ᵥ (b k : Fin g → O)) := by rw [this]
      _ = t i a • (b k : Fin g → O) := by rw [Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec, this]
  · have hz : ∀ j, j ≠ i → e j *ᵥ w = 0 := by
      intro j hj
      obtain ⟨a, ha⟩ := hd j i hj
      have h5 : (t j a - t i a) • (e j *ᵥ w) = 0 := by
        rw [sub_smul, ← Matrix.smul_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, sub_self]
      exact (ha.smul_eq_zero).1 h5
    have hwN : w ∈ N := by
      refine ⟨w, ?_⟩
      rw [Matrix.mulVecLin_apply]
      calc e i *ᵥ w = ∑ j, e j *ᵥ w := by
            rw [Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)]
        _ = w := by rw [← Matrix.sum_mulVec, h2, Matrix.one_mulVec]
    refine ⟨b.equivFun ⟨w, hwN⟩, ?_, fun c hc => ?_⟩
    · have := congrArg Subtype.val (b.sum_equivFun ⟨w, hwN⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum] using this
    · have : b.equivFun.symm c = ⟨w, hwN⟩ := by
        apply Subtype.ext
        rw [Module.Basis.equivFun_symm_apply]
        simpa using hc
      rw [← this, LinearEquiv.apply_symm_apply]
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) [IsLocalRing O], H.P = 0 → H.PL = 0 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (τ : Fin U.m ≃ (OE →+* O)) (ε : Fin U.m → O ⊗[ℤ] OE), (∀ i x, U.sg i x = tauExt (τ i) x) ∧ (∀ i, U.r i = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (τ i))) ∧ CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i, τ (U.cj i) = (τ i).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) ∧ ∀ i j, (∀ a, τ j a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O) → U.φ i = j := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ cp _ g H _ hP hPL hdisc
  obtain ⟨m, t, ε, φ, hε, he, hd, hφ⟩ := GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius p C v O hv OE hdisc
  let inc : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let ρT : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Ix g) (Ix g) O := (algebraMap ℤ_[p] O).mapMatrix.comp H.ρ.toRingHom
  obtain ⟨eT, hT1, hT2, hT3⟩ := exists_eigen_idem (fun i => t i) ε hε he (ρT.comp inc)
  obtain ⟨eL, hL1, hL2, hL3⟩ := exists_eigen_idem (fun i => t i) ε hε he (H.ρL.comp inc)
  have hρT : ∀ c : ℤ_[p], ρT (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Ix g) (Ix g) O) := by
    intro c
    have : H.ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] _ c := H.ρ.commutes c
    change (H.ρ (c ⊗ₜ[ℤ] 1)).map (algebraMap ℤ_[p] O) = _
    rw [this]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  have hρL : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) :=
    fun c => (padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
      (H.ρL.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] OE))) c
  let st : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  let cj : Fin m → Fin m := fun i => t.symm ((t i).comp st)
  have hcj : Function.Involutive cj := by
    intro i
    apply t.injective
    ext a
    simp [cj, st]
  have hlt : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → v (algebraMap O C x) < 1 := by
    intro x hx
    refine lt_of_le_of_ne (hv.map_le_one x) fun h => hx ?_
    exact hv.isUnit_of_one' h
  have hone : ∀ (s : OE →+* O) (a : OE), tauExt (p := p) s (1 ⊗ₜ[ℤ] a) = s a := by
    intro s a
    simp [tauExt]
  refine ⟨{ m := m
            sg := fun i => (tauExt (t i)).toRingHom
            εT := eT
            εL := eL
            cj := hcj.toPerm
            φ := φ
            r := fun i => eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (t i))
            noPad := ⟨hP, hPL⟩
            εT_orth := hT1
            εT_sum := hT2
            εL_orth := hL1
            εL_sum := hL2
            εT_eig := fun a i => eigen_ext ρT hρT (t i) (eT i) (fun b => hT3 b i) a
            εL_eig := fun a i => eigen_ext H.ρL hρL (t i) (eL i) (fun b => hL3 b i) a
            conj := fun i a => ?_
            frob := fun i a => hlt _ (frob_ext hp.out _ _ (hφ i) a)
            distinct := fun i j hij => ?_
            rank := fun i => ?_ }, t, ε, fun _ _ => rfl, fun _ => rfl, hε, he, fun i => ?_, fun i j h => ?_⟩
  · have h1 : t (hcj.toPerm cj i) = (t i).comp st := t.apply_symm_apply _
    change tauExt (t (hcj.toPerm cj i)) a = tauExt (t i) (sigE p OE a)
    rw [h1]
    exact ((embeddings_idempotents_conjugation p C v O hv OE).2.2 (t i) a).1
  · obtain ⟨a, ha⟩ := hd i j hij
    refine ⟨1 ⊗ₜ[ℤ] a, ?_⟩
    change v (algebraMap O C (tauExt (t i) (1 ⊗ₜ[ℤ] a) - tauExt (t j) (1 ⊗ₜ[ℤ] a))) = 1
    rw [hone, hone]
    exact hv.one_of_isUnit ha
  · obtain ⟨n, W, hW, hn⟩ := exists_eigB (fun i => t i) hd (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) eL hL1 hL2 hL3 i
    have := (eigB_res_surjective C v O hv OE g n _ (t i) W hW).2.2
    rw [← this] at hn
    exact hn
  · exact t.apply_symm_apply _
  · by_contra hne
    obtain ⟨a, ha⟩ := hd (φ i) j hne
    have := Ideal.sub_mem _ (hφ i a) (h a)
    rw [sub_sub_sub_cancel_right] at this
    exact this ha
end GlobalTheory.ChF
