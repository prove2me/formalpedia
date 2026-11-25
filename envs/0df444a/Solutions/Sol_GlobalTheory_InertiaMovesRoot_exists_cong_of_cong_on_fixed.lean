-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:51:21.383891+00:00
-- url     : https://prove2.me/submissions/4b61ee1c-a4d1-4e63-81cf-d1255925ffae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution {R S G : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] (Q : Ideal S) [Q.IsPrime]
    (g : G) (hg : ∀ b : S, (∀ k ∈ H, k • b = b) → g • b - b ∈ Q) :
    ∃ k ∈ H, ∃ k' ∈ H, ∀ b : S, (k' * g * k) • b - b ∈ Q := by
  let R' := FixedPoints.subalgebra R S H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : S) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' S := ⟨fun k r b => by
    change (k : G) • ((r : S) * b) = (r : S) * (k : G) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' S H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : (g⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  obtain ⟨k, hk⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R') (G := H)
    Q (g⁻¹ • Q) (by
      ext b
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      have := hg b (hR' b)
      change (b : S) ∈ Q ↔ g • (b : S) ∈ Q
      exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩)
  have hQ : (g * k) • Q = Q := by
    have hk2 : g⁻¹ • Q = (k : G) • Q := hk
    rw [mul_smul, ← hk2, smul_inv_smul]
  let φ : (S ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (S ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G S (g * k)) hQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q ((g * k) • (r : S)) = Ideal.Quotient.mk Q (r : S)
      rw [Ideal.Quotient.eq, mul_smul, hR' r k k.2]
      exact hg r (hR' r))
  obtain ⟨⟨k', hk'Q⟩, hk'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨k, k.2, k'⁻¹, inv_mem k'.2, fun b => ?_⟩
  have h1 : Ideal.Quotient.mk Q ((k' : G) • b) = Ideal.Quotient.mk Q ((g * k) • b) :=
    DFunLike.congr_fun hk' (Ideal.Quotient.mk Q b)
  rw [eq_comm, Ideal.Quotient.eq] at h1
  have h2 : (k' : G) • Q = Q := hk'Q
  rw [← h2, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, smul_smul] at h1
  rwa [mul_assoc]
end GlobalTheory.InertiaMovesRoot
