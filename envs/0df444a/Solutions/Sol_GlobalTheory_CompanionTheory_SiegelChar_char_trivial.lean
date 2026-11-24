-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.char_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:54.766026+00:00
-- url     : https://prove2.me/submissions/a8ae3a56-0241-49ea-ac31-4d8f7bcf76fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_lower_triv
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_cell_triv
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelChar_triv_of_cell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [Invertible (2 : F)] (E : Type) [CommRing E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (β ν : Type) [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] (J : Matrix β β E) (Cy : Matrix β ν E), IsQuad c ξ → IsHerm c J → IsLagr c J Cy → ∀ lam : UG c J →* ℂˣ, (∀ (p : UG c J) (t : GL ν E), ((p : GL β E) : Matrix β β E) * Cy = Cy * (t : Matrix ν ν E) → lam p = 1) → lam = 1 := by
  intro F _ _ _ E _ _ c ξ β ν _ _ _ _ J Cy hQ hH hL lam hpar
  classical
  obtain ⟨b, -, -⟩ := hQ.basis
  haveI : Module.Finite F E := Module.Finite.of_basis b
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨hJh, hJdet⟩ := hH
  obtain ⟨hCy, Cx, M, hCx, hPM, hMP⟩ := hL
  obtain ⟨Ji, hJi⟩ : ∃ Ji : Matrix β β E, Ji = J⁻¹ := ⟨_, rfl⟩
  have hJJi : J * Ji = 1 := by rw [hJi]; exact Matrix.mul_nonsing_inv J hJdet
  have hJiJ : Ji * J = 1 := by rw [hJi]; exact Matrix.nonsing_inv_mul J hJdet
  let cm : Matrix β β E →+* Matrix β β E := (c.toRingHom).mapMatrix
  have hcm : ∀ x : Matrix β β E, cm x = x.map c := fun x => rfl
  let σ : Matrix β β E →+ Matrix β β E := AddMonoidHom.mk' (fun x => (J * cm x * Ji)ᵀ) (by
    intro x y
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add])
  have hσ : ∀ x, σ x = (J * cm x * Ji)ᵀ := fun x => rfl
  have hcm_smul : ∀ (a : E) (x : Matrix β β E), cm (a • x) = c a • cm x := by
    intro a x
    ext i j
    simp [hcm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hsm : ∀ (a : E) (x : Matrix β β E), σ (a • x) = c a • σ x := by
    intro a x
    rw [hσ, hσ, hcm_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul]
  have hmul : ∀ x y : Matrix β β E, σ (x * y) = σ y * σ x := by
    intro x y
    rw [hσ, hσ, hσ, map_mul, ← Matrix.transpose_mul]
    congr 1
    calc J * (cm x * cm y) * Ji = J * cm x * (Ji * J) * cm y * Ji := by
          rw [hJiJ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = J * cm x * Ji * (J * cm y * Ji) := by simp only [Matrix.mul_assoc]
  have h1 : σ 1 = 1 := by rw [hσ, map_one, Matrix.mul_one, hJJi, Matrix.transpose_one]
  have hkey : ∀ x : Matrix β β E, σ x * x = Jiᵀ * (xᵀ * J * x.map c)ᵀ := by
    intro x
    rw [hσ, hcm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hJt : Jᵀ * Jiᵀ = 1 := by rw [← Matrix.transpose_mul, hJiJ, Matrix.transpose_one]
  have hJt' : Jiᵀ * Jᵀ = 1 := by rw [← Matrix.transpose_mul, hJJi, Matrix.transpose_one]
  have hunitary : ∀ x : Matrix β β E, σ x * x = 1 ↔ xᵀ * J * x.map c = J := by
    intro x
    rw [hkey]
    constructor
    · intro h
      have h' : (xᵀ * J * x.map c)ᵀ = Jᵀ := by
        calc (xᵀ * J * x.map c)ᵀ = Jᵀ * (Jiᵀ * (xᵀ * J * x.map c)ᵀ) := by
              rw [← Matrix.mul_assoc, hJt, Matrix.one_mul]
          _ = Jᵀ := by rw [h, Matrix.mul_one]
      exact Matrix.transpose_inj.mp h'
    · intro h
      rw [h, hJt']
  let φ : ↥(UG c J) →* Matrix β β E := (Units.coeHom (Matrix β β E)).comp (UG c J).subtype
  have hφ : ∀ g : ↥(UG c J), φ g = ((g : GL β E) : Matrix β β E) := fun g => rfl
  have hu : ∀ g : ↥(UG c J), σ (φ g) * φ g = 1 := fun g => (hunitary _).mpr g.2
  have hsurj : ∀ x, σ x * x = 1 → ∃ g, φ g = x := by
    intro x hx
    have hxσ : x * σ x = 1 := mul_eq_one_comm.mp hx
    exact ⟨⟨⟨x, σ x, hxσ, hx⟩, (hunitary x).mp hx⟩, rfl⟩
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Units.ext h)
  obtain ⟨Mt, hMt⟩ : ∃ Mt, Mt = M.toRows₁ := ⟨_, rfl⟩
  obtain ⟨Mb, hMb⟩ : ∃ Mb, Mb = M.toRows₂ := ⟨_, rfl⟩
  have hM : M = Matrix.fromRows Mt Mb := by rw [hMt, hMb, Matrix.fromRows_toRows]
  have hPM' : Cy * Mt + Cx * Mb = 1 := by rw [hM, Matrix.fromCols_mul_fromRows] at hPM; exact hPM
  rw [hM, Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hMP
  obtain ⟨hMtCy, hMtCx, hMbCy, hMbCx⟩ := hMP
  obtain ⟨e, he⟩ : ∃ e : Matrix β β E, e = Cy * Mt := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Matrix β β E, f = Cx * Mb := ⟨_, rfl⟩
  have hef : e + f = 1 := by rw [he, hf, hPM']
  have hee : e * e = e := by
    rw [he, Matrix.mul_assoc Cy Mt (Cy * Mt), ← Matrix.mul_assoc Mt Cy Mt, hMtCy, Matrix.one_mul]
  have hff : f * f = f := by
    rw [hf, Matrix.mul_assoc Cx Mb (Cx * Mb), ← Matrix.mul_assoc Mb Cx Mb, hMbCx, Matrix.one_mul]
  have hef0 : e * f = 0 := by
    rw [he, hf, Matrix.mul_assoc Cy Mt (Cx * Mb), ← Matrix.mul_assoc Mt Cx Mb, hMtCx, Matrix.zero_mul,
      Matrix.mul_zero]
  have hfe0 : f * e = 0 := by
    rw [he, hf, Matrix.mul_assoc Cx Mb (Cy * Mt), ← Matrix.mul_assoc Mb Cy Mt, hMbCy, Matrix.zero_mul,
      Matrix.mul_zero]
  have hefc : Cy.map c * Mt.map c + Cx.map c * Mb.map c = 1 := by
    have h := congrArg cm hPM'
    rw [map_add, map_one, hcm, hcm, Matrix.map_mul, Matrix.map_mul] at h
    exact h
  have heft : Mtᵀ * Cyᵀ + Mbᵀ * Cxᵀ = 1 := by
    have h := congrArg Matrix.transpose hPM'
    rwa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one] at h
  have K : J * (Cx.map c * Mb.map c) = Mtᵀ * Cyᵀ * J := by
    have A1 : Mtᵀ * Cyᵀ * J = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
      calc Mtᵀ * Cyᵀ * J = Mtᵀ * Cyᵀ * J * (Cy.map c * Mt.map c + Cx.map c * Mb.map c) := by
            rw [hefc, Matrix.mul_one]
        _ = Mtᵀ * (Cyᵀ * J * Cy.map c) * Mt.map c + Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            simp only [Matrix.mul_add, Matrix.mul_assoc]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            rw [hCy, Matrix.mul_zero, Matrix.zero_mul, zero_add]
    have A2 : J * (Cx.map c * Mb.map c) = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
      calc J * (Cx.map c * Mb.map c) = (Mtᵀ * Cyᵀ + Mbᵀ * Cxᵀ) * J * (Cx.map c * Mb.map c) := by
            rw [heft, Matrix.one_mul]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c + Mbᵀ * (Cxᵀ * J * Cx.map c) * Mb.map c := by
            simp only [Matrix.add_mul, Matrix.mul_assoc]
        _ = Mtᵀ * Cyᵀ * J * Cx.map c * Mb.map c := by
            rw [hCx, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [A2, ← A1]
  have hσe : σ e = f := by
    have B1 : J * (Cy.map c * Mt.map c) = Mbᵀ * Cxᵀ * J := by
      have h1' : Cy.map c * Mt.map c = 1 - Cx.map c * Mb.map c := eq_sub_of_add_eq hefc
      have h2' : Mbᵀ * Cxᵀ = 1 - Mtᵀ * Cyᵀ := eq_sub_of_add_eq' heft
      rw [h1', Matrix.mul_sub, Matrix.mul_one, K, h2', Matrix.sub_mul, Matrix.one_mul]
    rw [he, hf, hσ, hcm, Matrix.map_mul, B1, Matrix.mul_assoc (Mbᵀ * Cxᵀ) J Ji, hJJi, Matrix.mul_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hσf : σ f = e := by
    rw [he, hf, hσ, hcm, Matrix.map_mul, K, Matrix.mul_assoc (Mtᵀ * Cyᵀ) J Ji, hJJi, Matrix.mul_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
  have hP : ∀ g : ↥(UG c J), f * φ g * e = 0 → lam g = 1 := by
    intro g hg
    obtain ⟨x, hx⟩ : ∃ x, x = φ g := ⟨_, rfl⟩
    rw [← hx] at hg
    have hxe : x * e = e * x * e := by
      calc x * e = (e + f) * x * e := by rw [hef, Matrix.one_mul]
        _ = e * x * e := by rw [Matrix.add_mul, Matrix.add_mul, hg, add_zero]
    have heCy : e * Cy = Cy := by rw [he, Matrix.mul_assoc, hMtCy, Matrix.mul_one]
    have hxCy : x * Cy = Cy * (Mt * x * Cy) := by
      calc x * Cy = x * (e * Cy) := by rw [heCy]
        _ = e * x * e * Cy := by rw [← Matrix.mul_assoc, hxe]
        _ = Cy * (Mt * x * Cy) := by
            rw [Matrix.mul_assoc (e * x) e Cy, heCy, he]
            simp only [Matrix.mul_assoc]
    have hexCy : e * (x * Cy) = x * Cy := by
      rw [hxCy, ← Matrix.mul_assoc, heCy]
    obtain ⟨xi, hxi⟩ : ∃ xi, xi = φ g⁻¹ := ⟨_, rfl⟩
    have hxxi : xi * x = 1 := by rw [hxi, hx, ← map_mul, inv_mul_cancel, map_one]
    have ht't : Mt * xi * Cy * (Mt * x * Cy) = 1 := by
      calc Mt * xi * Cy * (Mt * x * Cy) = Mt * xi * ((Cy * Mt) * (x * Cy)) := by
            simp only [Matrix.mul_assoc]
        _ = Mt * xi * (x * Cy) := by rw [← he, hexCy]
        _ = Mt * (xi * x) * Cy := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hxxi, Matrix.mul_one, hMtCy]
    have htt' : Mt * x * Cy * (Mt * xi * Cy) = 1 := mul_eq_one_comm.mp ht't
    apply hpar g ⟨Mt * x * Cy, Mt * xi * Cy, htt', ht't⟩
    show φ g * Cy = Cy * (Mt * x * Cy)
    rw [← hx]
    exact hxCy
  have hi2 : (2 : E) * algebraMap F E (⅟2) = 1 := by
    rw [← map_ofNat (algebraMap F E) 2, ← map_mul, mul_invOf_self, map_one]
  have h3F : (3 : F) ≠ 0 := three_ne_zero
  have hi3 : (3 : E) * algebraMap F E (3⁻¹) = 1 := by
    rw [← map_ofNat (algebraMap F E) 3, ← map_mul, mul_inv_cancel₀ h3F, map_one]
  have c2 : c 2 = 2 := map_ofNat c 2
  have ci2 : c (algebraMap F E (⅟2)) = algebraMap F E (⅟2) := c.commutes _
  have ci3 : c (algebraMap F E (3⁻¹)) = algebraMap F E (3⁻¹) := c.commutes _
  have hlow : ∀ s, e * s = 0 → s * f = 0 → σ s = -s → ∃ n, φ n = 1 + s ∧ lam n = 1 :=
    fun s hes hsf0 hs => lower_triv (c := ⇑c) (σ := σ) (φ := φ) hsm h1 hi2 hi3 c2 ci2 ci3 hinj hsurj
      hef hee hff hef0 hfe0 hσe hσf lam s hes hsf0 hs
  have hcell : ∀ g, IsUnit (φ g * e + f) → lam g = 1 :=
    fun g hg => cell_triv (σ := σ) (φ := φ) hmul h1 hu hef hee hff hef0 hfe0 hσe hσf lam hlow hP g hg
  have h2E : IsUnit (2 : E) := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (isUnit_of_invertible (2 : F)).map _
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  exact triv_of_cell (F := F) (c := c) hQ.unit h2E hQ.anti hsm hmul h1 hu hsurj hef hee hff hef0 hfe0 lam hcell g
end GlobalTheory.CompanionTheory.SiegelChar
