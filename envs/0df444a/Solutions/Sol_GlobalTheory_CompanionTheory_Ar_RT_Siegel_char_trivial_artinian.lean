-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.Siegel.char_trivial_artinian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:28.920503+00:00
-- url     : https://prove2.me/submissions/0f175ded-27d4-490d-8f43-5b3f98eb08db

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_triv_of_cell
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_cell_triv
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_lower_triv
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_triv_of_cell


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.WeilM GlobalTheory.CompanionTheory.SiegelChar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.Siegel
namespace GlobalTheory.CompanionTheory.Ar.RT.Siegel
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [CommRing E] [IsArtinianRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsUnit ξ → c ξ = -ξ → (∀ x, c (c x) = x) → IsUnit J.det → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  intro F _ _ E _ _ _ c ξ β ν _ _ _ _ J Cy hξ hanti hinvol hJ hL lam hlam
  obtain ⟨hy, Cx, M, hx, hM1, hM2⟩ := hL
  have cmul : ∀ {l m n : Type} [Fintype m] (a : Matrix l m E) (b : Matrix m n E), (a * b).map c = a.map c * b.map c :=
    fun a b => Matrix.map_mul (f := c.toRingHom)
  have cone : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have cc : ∀ a : Matrix β β E, (a.map c).map c = a := fun a => by ext i j; exact hinvol _
  have J1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  have J2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hJ
  let σ : Matrix β β E →+ Matrix β β E := AddMonoidHom.mk' (fun x => (J⁻¹ * xᵀ * J).map c) (fun a b => by
    rw [transpose_add, mul_add, add_mul, Matrix.map_add _ (map_add c)])
  have hσ : ∀ x, σ x = (J⁻¹ * xᵀ * J).map c := fun _ => rfl
  have hsm : ∀ (a : E) x, σ (a • x) = c a • σ x := fun a x => by
    rw [hσ, hσ, transpose_smul, mul_smul_comm, smul_mul_assoc]
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hmul : ∀ x y, σ (x * y) = σ y * σ x := fun x y => by
    rw [hσ, hσ, hσ, ← cmul, transpose_mul]
    congr 1
    calc _ = J⁻¹ * yᵀ * (J * J⁻¹) * xᵀ * J := by rw [J1, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have h1 : σ 1 = 1 := by rw [hσ, transpose_one, mul_one, J2, cone]
  have hform : ∀ x y, σ x * y = (J⁻¹ * (xᵀ * J * y.map c)).map c := fun x y => by
    rw [hσ, ← mul_assoc, ← mul_assoc, cmul _ (y.map c), cc]
  let φ : UG c J →* Matrix β β E := (Units.coeHom _).comp (UG c J).subtype
  have hφ : ∀ g, φ g = ((g : GL β E) : Matrix β β E) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  have hu : ∀ g, σ (φ g) * φ g = 1 := fun g => by
    rw [hform, show (φ g)ᵀ * J * (φ g).map c = J from g.2, J2, cone]
  have hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x := fun x h => by
    refine ⟨⟨⟨x, σ x, mul_eq_one_comm.mp h, h⟩, ?_⟩, rfl⟩
    change xᵀ * J * x.map c = J
    have := congrArg (fun z : Matrix β β E => J * z.map c) h
    simp only [hform, cc, cone] at this
    rwa [← mul_assoc, J1, one_mul, mul_one] at this
  rw [← Matrix.fromRows_toRows M] at hM1 hM2
  generalize M.toRows₁ = M1 at hM1 hM2
  generalize M.toRows₂ = M2 at hM1 hM2
  rw [fromCols_mul_fromRows] at hM1
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_inj] at hM2
  obtain ⟨m11, m12, m21, m22⟩ := hM2
  have hee : (Cy * M1) * (Cy * M1) = Cy * M1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M1, m11, Matrix.one_mul]
  have hff : (Cx * M2) * (Cx * M2) = Cx * M2 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M2, m22, Matrix.one_mul]
  have hef0 : (Cy * M1) * (Cx * M2) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M1, m12, Matrix.zero_mul, Matrix.mul_zero]
  have hfe0 : (Cx * M2) * (Cy * M1) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M2, m21, Matrix.zero_mul, Matrix.mul_zero]
  have iso : ∀ (C : Matrix β ν E) (N : Matrix ν β E), Cᵀ * J * C.map c = 0 → σ (C * N) * (C * N) = 0 := fun C N h => by
    rw [hform, transpose_mul, cmul C N]
    have : Nᵀ * Cᵀ * J * (C.map c * N.map c) = Nᵀ * (Cᵀ * J * C.map c) * N.map c := by simp only [Matrix.mul_assoc]
    rw [this, h, Matrix.mul_zero, Matrix.zero_mul, mul_zero, Matrix.map_zero _ (map_zero c)]
  have ie := iso Cy M1 hy
  have if' := iso Cx M2 hx
  have hP : ∀ g, (Cx * M2) * φ g * (Cy * M1) = 0 → lam g = 1 := fun g h => by
    have a : φ g * Cy = Cy * (M1 * φ g * Cy) := by
      have h' : (Cx * M2) * φ g * Cy = 0 := by
        have := congrArg (· * Cy) h
        simp only [Matrix.mul_assoc, m11, Matrix.mul_one, Matrix.zero_mul] at this ⊢
        exact this
      calc φ g * Cy = (Cy * M1 + Cx * M2) * φ g * Cy := by rw [hM1, one_mul]
        _ = _ := by rw [add_mul, Matrix.add_mul, h', add_zero]; simp only [Matrix.mul_assoc]
    have b : (M1 * φ g⁻¹ * Cy) * (M1 * φ g * Cy) = 1 := by
      rw [Matrix.mul_assoc, ← a, Matrix.mul_assoc, ← Matrix.mul_assoc (φ g⁻¹), ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mul, m11]
    exact hlam g ⟨_, _, mul_eq_one_comm.mp b, b⟩ a
  generalize Cy * M1 = e at *
  generalize Cx * M2 = f at *
  have hsum : σ e + σ f = 1 := by rw [← map_add, hM1, h1]
  have hse : σ e = f := by
    calc σ e = σ e * (e + f) + σ f * f := by rw [hM1, if', mul_one, add_zero]
      _ = (σ e + σ f) * f := by rw [mul_add, ie, zero_add, add_mul]
      _ = f := by rw [hsum, one_mul]
  have hsf : σ f = e := by
    rw [hse, ← hM1, add_comm e] at hsum
    exact add_left_cancel hsum
  have h2 : (2 : E) * algebraMap F E 2⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  have h3 : (3 : E) * algebraMap F E 3⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap F E) 3, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  ext g
  rw [triv_of_cell hξ (IsUnit.of_mul_eq_one _ h2) hanti hsm hmul h1 hu hsurj hM1 hee hff hef0 hfe0 lam
    (cell_triv hmul h1 hu hM1 hee hff hef0 hfe0 hse hsf lam
      (lower_triv hsm h1 h2 h3 (map_ofNat c 2) (c.commutes _) (c.commutes _) hinj hsurj hM1 hee hff hef0 hfe0 hse hsf lam)
      hP) g]
  rfl
end GlobalTheory.CompanionTheory.Ar.RT.Siegel
