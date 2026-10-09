-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_10
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:01:16.840978+00:00
-- url     : https://prove2.me/submissions/86873e0b-7102-4cb6-9b11-caa70cf737ca

import Definitions.Def_SidorenkoFiniteGeometryCertificates08
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0029]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0030]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0107]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0110]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0111]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0127]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0136]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0193]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0196]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0205]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0210]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0212]
  [p17 : OAI.SidorenkoCounterexample.ProofCertificate_0214]
  [p18 : OAI.SidorenkoCounterexample.ProofCertificate_0215]
  [p19 : OAI.SidorenkoCounterexample.ProofCertificate_0228]
  [p20 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
  [p21 : OAI.SidorenkoCounterexample.ProofCertificate_0231]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericCounts
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section IsotropicCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AvoidanceCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end AvoidanceCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end ContainmentAvoidance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end CommonSpaceLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [Fintype K] [Finite E]
theorem certificate_proof_0232 : Nat.card (E ≃ₗ[K] E) ≤
    Fintype.card K ^ (finrank K E * finrank K E) := by
  rw [linearAut_card]
  calc
    _ ≤ ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => Nat.sub_le _ _)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]

private instance certificate_instance_0232 : OAI.SidorenkoCounterexample.ProofCertificate_0232 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0232 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6

theorem certificate_proof_0233 (U V : Submodule K E) (hUV : IsCompl U V) :
    (Fintype.card K : ℝ)^(2*finrank K U*finrank K V) ≤
      2^(finrank K E)*(Nat.card (PairLinearOrbit U V) : ℝ) ∧
    (Nat.card (PairLinearOrbit U V) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*finrank K U*finrank K V) := by
  let u := finrank K U
  let v := finrank K V
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+v = n := Submodule.finrank_add_eq_of_isCompl hUV
  have he : n*n = 2*u*v + (u*u+v*v) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (PairLinearOrbit U V) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast pairLinearOrbit_card_identity U V hUV
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v))) := by gcongr
      _ = _ := by rw [←pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = (Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v)) := by rw [pow_add]
      _ ≤ (Nat.card (PairLinearOrbit U V) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*(2^v*Nat.card (V ≃ₗ[K] V))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn,pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring

private instance certificate_instance_0233 : OAI.SidorenkoCounterexample.ProofCertificate_0233 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0233 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end Decompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
theorem certificate_proof_0234 (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) (u : U) (v : V) (w : W) :
    tripleSumEquiv U V W hU hVW (u,(v,w)) = u.val+(v.val+w.val) := rfl

private instance certificate_instance_0234 : OAI.SidorenkoCounterexample.ProofCertificate_0234 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0234 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0235 (U : Submodule K E) (e : E ≃ₗ[K] E) (g : U ≃ₗ[K] U)
    (h : ∀ u : U, e u.val = (g u).val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    change e u ∈ U
    rw [h ⟨u,hu⟩]
    exact (g ⟨u,hu⟩).property
  · intro hx
    refine ⟨(g.symm ⟨x,hx⟩).val,(g.symm ⟨x,hx⟩).property,?_⟩
    exact (h _).trans (congrArg Subtype.val (g.apply_symm_apply ⟨x,hx⟩))

private instance certificate_instance_0235 : OAI.SidorenkoCounterexample.ProofCertificate_0235 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0235 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0236 (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Function.Bijective (tripleLinearStabilizerRestriction U V W) := by
  let c := tripleSumEquiv U V W hU hVW
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    obtain ⟨⟨u,v,w⟩,rfl⟩ := c.surjective x
    have h₁ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.1 u).val) hh
    have h₂ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.1 v).val) hh
    have h₃ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.2 w).val) hh
    change e.val u.val = f.val u.val at h₁
    change e.val v.val = f.val v.val at h₂
    change e.val w.val = f.val w.val at h₃
    change e.val (u.val+(v.val+w.val)) = f.val (u.val+(v.val+w.val))
    simp only [map_add,h₁,h₂,h₃]
  · intro g
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr (g.2.1.prodCongr g.2.2)).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,(0,0)) = u.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2.1 v).val := by
      have hc : c (0,(v,0)) = v.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heW (w : W) : e w.val = (g.2.2 w).val := by
      have hc : c (0,(0,w)) = w.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm w.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    refine ⟨⟨e,map_eq_of_restriction_aut U e g.1 heU,
      map_eq_of_restriction_aut V e g.2.1 heV,map_eq_of_restriction_aut W e g.2.2 heW⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · apply Prod.ext
      · ext v
        exact heV v
      · ext w
        exact heW w

private instance certificate_instance_0236 : OAI.SidorenkoCounterexample.ProofCertificate_0236 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0236 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

variable [Finite E]
theorem certificate_proof_0237 (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Nat.card (TripleLinearOrbit U V W) *
      (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (TripleLinearOrbit U V W)
  have hc : Nat.card (TripleLinearStabilizer U V W) =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (tripleLinearStabilizerRestriction_bijective U V W hU hVW)),
      Nat.card_prod,Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleLinearOrbitMap U V W))).symm
  rw [Nat.card_sigma] at he
  have hf (p : TripleLinearOrbit U V W) : Nat.card {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) :=
    (Nat.card_congr (tripleLinearOrbitFiberEquiv U V W p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm

private instance certificate_instance_0237 : OAI.SidorenkoCounterexample.ProofCertificate_0237 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0237 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

variable [Fintype K]
theorem certificate_proof_0238 (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      2^(finrank K E)*(Nat.card (TripleLinearOrbit U V W) : ℝ) ∧
    (Nat.card (TripleLinearOrbit U V W) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  let u := finrank K U
  let v := finrank K V
  let w := finrank K W
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+(v+w) = n := by
    simpa only [Module.finrank_prod] using (tripleSumEquiv U V W hU hVW).finrank_eq
  have he : n*n = 2*(u*v+u*w+v*w) + (u*u+(v*v+w*w)) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (TripleLinearOrbit U V W) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast tripleLinearOrbit_card_identity U V W hU hVW
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,v]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hw : (Nat.card (W ≃ₗ[K] W) : ℝ) ≤ q^(w*w) := by dsimp [q,w]; exact_mod_cast linearAut_card_upper (K := K) (E := W)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,v]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hw' : q^(w*w) ≤ 2^w*(Nat.card (W ≃ₗ[K] W) : ℝ) := by dsimp [q,w]; exact_mod_cast linearAut_card_lower (K := K) (E := W)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w)))) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = (Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w))) := by simp only [pow_add]
      _ ≤ (Nat.card (TripleLinearOrbit U V W) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*((2^v*Nat.card (V ≃ₗ[K] V))*(2^w*Nat.card (W ≃ₗ[K] W)))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn]; simp only [pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring

private instance certificate_instance_0238 : OAI.SidorenkoCounterexample.ProofCertificate_0238 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0238 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end TripleDecompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type}
theorem certificate_proof_0239 [Finite A] [Finite B] [Finite C] [Finite D]
    (f : A → B) (g : C → D)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)
    (hg : ∀ d, Nat.card {c : C // g c = d} * Nat.card D = Nat.card C)
    (p : B × D) :
    Nat.card {x : A × C // (f x.1,g x.2) = p} * Nat.card (B × D) = Nat.card (A × C) := by
  rcases p with ⟨b,d⟩
  rw [Nat.card_congr (prodFiberEquiv f g b d),Nat.card_prod,Nat.card_prod,Nat.card_prod]
  calc
    _ = (Nat.card {a : A // f a = b} * Nat.card B) *
      (Nat.card {c : C // g c = d} * Nat.card D) := by ring
    _ = _ := by rw [hf,hg]

private instance certificate_instance_0239 : OAI.SidorenkoCounterexample.ProofCertificate_0239 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0239 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0240 [Finite A] [Finite B] (f : A → B)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A) (P : B → Prop) :
    Nat.card {a : A // P (f a)} * Nat.card B = Nat.card {b : B // P b} * Nat.card A := by
  classical
  let := Fintype.ofFinite {b : B // P b}
  let e : {a : A // P (f a)} ≃ Σ b : {b : B // P b}, {a : A // f a = b.val} :=
    { toFun := fun a => ⟨⟨f a.val,a.property⟩,⟨a.val,rfl⟩⟩
      invFun := fun b => ⟨b.2.val,by rw [b.2.property]; exact b.1.property⟩
      left_inv := fun a => rfl
      right_inv := by rintro ⟨⟨b,hb⟩,a,ha⟩; dsimp at ha; subst b; rfl }
  rw [Nat.card_congr e,Nat.card_sigma,Finset.sum_mul]
  simp only [Nat.card_eq_fintype_card] at hf
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

private instance certificate_instance_0240 : OAI.SidorenkoCounterexample.ProofCertificate_0240 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0240 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6

end UniformCounts
section ExactPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)
theorem certificate_proof_0241
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLA : L ⊓ S = A) (hMB : M ⊓ S = B) (hAB : A ⊔ B = S)
    (hr : reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥) :
    L ⊓ M = A ⊓ B := by
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ ω.orthogonal S := by
      intro y hy
      rw [←hAB] at hy
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hy
      have haL : a ∈ L := (hLA.symm ▸ ha : a ∈ L ⊓ S).1
      have hbM : b ∈ M := (hMB.symm ▸ hb : b ∈ M ⊓ S).1
      rw [map_add,LinearMap.add_apply,(hL.ge hx.1) a haL,(hM.ge hx.2) b hbM,add_zero]
    have hxq : (reductionKernel ω S).mkQ ⟨x,hxP⟩ = 0 := by
      have hmem : (reductionKernel ω S).mkQ ⟨x,hxP⟩ ∈
          reduceSubspace ω S L ⊓ reduceSubspace ω S M :=
        ⟨⟨⟨x,hxP⟩,hx.1,rfl⟩,⟨⟨x,hxP⟩,hx.2,rfl⟩⟩
      simpa only [hr,Submodule.mem_bot] using hmem
    have hxS : x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxq
    exact ⟨hLA ▸ (⟨hx.1,hxS⟩ : x ∈ L ⊓ S),hMB ▸ (⟨hx.2,hxS⟩ : x ∈ M ⊓ S)⟩
  · intro x hx
    exact ⟨(hLA.symm ▸ hx.1 : x ∈ L ⊓ S).1,(hMB.symm ▸ hx.2 : x ∈ M ⊓ S).1⟩

private instance certificate_instance_0241 : OAI.SidorenkoCounterexample.ProofCertificate_0241 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16
  exact @certificate_proof_0241 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16

end ExactPairs
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
theorem certificate_proof_0242 (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) ((L ⊓ N) ⊔ (M ⊓ N)) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨hx.1,(show (L ⊓ N) ⊔ (M ⊓ N) ≤ N from sup_le inf_le_right inf_le_right) hx.2⟩
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩

private instance certificate_instance_0242 : OAI.SidorenkoCounterexample.ProofCertificate_0242 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0242 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0243 (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    L ⊓ triplePairSum L M N = (L ⊓ M) ⊔ (L ⊓ N) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,v,hv,hxuv⟩ := Submodule.mem_sup.mp hx.2
    have huL : u ∈ L := (show (L ⊓ M) ⊔ (L ⊓ N) ≤ L from sup_le inf_le_left inf_le_left) hu
    have hvL : v ∈ L := by
      have hh := L.sub_mem hx.1 huL
      rw [←hxuv,add_sub_cancel_left] at hh
      exact hh
    have hz : v = 0 := by simpa only [Submodule.mem_bot] using h0.le ⟨⟨hvL,hv.1⟩,hv.2⟩
    have hxu : u = x := by simpa only [hz,add_zero] using hxuv
    exact hxu ▸ hu
  · exact le_inf (sup_le inf_le_left inf_le_left) le_sup_left

private instance certificate_instance_0243 : OAI.SidorenkoCounterexample.ProofCertificate_0243 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0243 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0244 (ω : LinearMap.BilinForm K E)
    (S L M : Submodule K E) (hS : S ≤ ω.orthogonal S) (hsplit : (L ⊓ S) ⊔ (M ⊓ S) = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = reduceSubspace ω S (L ⊓ M) := by
  apply le_antisymm
  · rintro x ⟨⟨l,hl,hlx⟩,⟨m,hm,hmx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-m) = 0 := by rw [map_sub,hlx,hmx,sub_self]
    have hdiff : l.val-m.val ∈ (L ⊓ S) ⊔ (M ⊓ S) := by
      rw [hsplit]
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hdiff
    have hla : l.val-a = m.val+b := by
      calc
        _ = (l.val-m.val)-a+m.val := by abel
        _ = (a+b)-a+m.val := by rw [hab]
        _ = _ := by abel
    have haP : a ∈ ω.orthogonal S := hS ha.2
    exact ⟨⟨l.val-a,(ω.orthogonal S).sub_mem l.property haP⟩,
      ⟨L.sub_mem hl ha.1,by change l.val-a ∈ M; rw [hla]; exact M.add_mem hm hb.1⟩,by
        change (reductionKernel ω S).mkQ (l-⟨a,haP⟩) = x
        have hz : (reductionKernel ω S).mkQ ⟨a,haP⟩ = 0 :=
          (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr ha.2
        rw [map_sub,hz,sub_zero,hlx]⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩

private instance certificate_instance_0244 : OAI.SidorenkoCounterexample.ProofCertificate_0244 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0244 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

end PairSpaceFacts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0245 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    Nat.card (OrderedTransversePair ω) = Nat.card (SymplecticLagrangian ω) *
      Fintype.card K^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  have hp := Nat.card_congr (orderedTransversePairEquiv canonicalSymplectic ω e he)
  rw [←hp,orderedTransversePair_card h2,hc,hd]

private instance certificate_instance_0245 : OAI.SidorenkoCounterexample.ProofCertificate_0245 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0245 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

theorem certificate_proof_0246 [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (SymplecticLagrangian ω) * (Fintype.card K^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hd : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hcard := fixedPairOrbit_card_lower ω L.val M.val N.val ha hω
    L.property M.property N.property hLM hLN hMN
  rw [hd] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection ω ha hω L.val M.val N.val
    L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,symplectic_orderedTransversePair_card ω
    (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD] at hi
  calc
    _ = (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        Fintype.card K^((D+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        (4^D * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^D * (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2) *
        Nat.card (FixedPairOrbit ω L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi

private instance certificate_instance_0246 : OAI.SidorenkoCounterexample.ProofCertificate_0246 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0246 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

theorem certificate_proof_0247 [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (SymplecticLagrangian ω) : ℝ)^3 ≤
      (4^D * lagrangianConstant D^2) * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hb := (symplecticLagrangian_card_bounds ω (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD).2
  have ho : (Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast symplectic_transverseTriple_card_lower ω ha hω D hD L M N hLM hLN hMN
  calc
    _ = (Nat.card (SymplecticLagrangian ω) : ℝ) * (Nat.card (SymplecticLagrangian ω) : ℝ)^2 := by ring
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ) *
      (lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2))^2 := by gcongr
    _ = lagrangianConstant D^2 * ((Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2) := by ring
    _ ≤ lagrangianConstant D^2 * (4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val)) :=
      mul_le_mul_of_nonneg_left ho (sq_nonneg _)
    _ = _ := by ring

private instance certificate_instance_0247 : OAI.SidorenkoCounterexample.ProofCertificate_0247 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18
  exact @certificate_proof_0247 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18

end GenericTransverseMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
theorem certificate_proof_0248 (S L : Submodule K E) (hLS : L ≤ S) :
    reduceSubspace ω S L = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr (hLS hy)

private instance certificate_instance_0248 : OAI.SidorenkoCounterexample.ProofCertificate_0248 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0248 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8

theorem certificate_proof_0249 (L M N : Submodule K E) :
    (L ⊓ triplePairSum L M N) ⊔ (M ⊓ triplePairSum L M N) = triplePairSum L M N := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  unfold triplePairSum
  apply sup_le (sup_le _ _) _
  · exact (le_inf inf_le_left (le_sup_left.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left (le_sup_right.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left le_sup_right).trans le_sup_right

private instance certificate_instance_0249 : OAI.SidorenkoCounterexample.ProofCertificate_0249 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0249 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0250 (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    reduceSubspace ω (triplePairSum L M N) L ⊓
      reduceSubspace ω (triplePairSum L M N) M = ⊥ := by
  rw [reduction_intersection_of_split_kernel ω _ L M
    (triplePairSum_isotropic ω L M N hL hM hN) (triplePairSum_split L M N)]
  exact reduceSubspace_eq_bot_of_le ω _ _ (le_sup_left.trans le_sup_left)

private instance certificate_instance_0250 : OAI.SidorenkoCounterexample.ProofCertificate_0250 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0250 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0251 (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    let S := triplePairSum L M N
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ ∧
    reduceSubspace ω S L ⊓ reduceSubspace ω S N = ⊥ ∧
    reduceSubspace ω S M ⊓ reduceSubspace ω S N = ⊥ := by
  dsimp only
  refine ⟨triplePairSum_reduce_pair ω L M N hL hM hN,?_,?_⟩
  · have hs : triplePairSum L N M = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm N M,sup_comm (L ⊓ N) (L ⊓ M)]
    have h := triplePairSum_reduce_pair ω L N M hL hN hM
    rw [hs] at h
    exact h
  · have hs : triplePairSum M N L = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm M L,inf_comm N L]
      ac_rfl
    have h := triplePairSum_reduce_pair ω M N L hM hN hL
    rw [hs] at h
    exact h

private instance certificate_instance_0251 : OAI.SidorenkoCounterexample.ProofCertificate_0251 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0251 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end ResidualTransversality
section LagrangianTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
theorem certificate_proof_0252 (p : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal p.val.1 = p.val.1 ∧ ω.orthogonal p.val.2.1 = p.val.2.1 ∧
      ω.orthogonal p.val.2.2 = p.val.2.2 := by
  obtain ⟨e,he,hL,hM,hN⟩ := p.property
  rw [←hL,←hM,←hN,orthogonal_map_of_isometry ω e he,orthogonal_map_of_isometry ω e he,
    orthogonal_map_of_isometry ω e he,L.property,M.property,N.property]
  exact ⟨rfl,rfl,rfl⟩

private instance certificate_instance_0252 : OAI.SidorenkoCounterexample.ProofCertificate_0252 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  exact @certificate_proof_0252 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9

end LagrangianTripleOrbit
section AvoidanceTripleCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
theorem certificate_proof_0253 (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (p : SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card {x // avoidanceTripleReduction ω S ha hω hS A B C x = p} *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha)) =
      Nat.card (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  exact uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS A hA)
    (uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS B hB)
      (avoidanceReduction_uniform ω S h2 ha hω hS C hC)) p

private instance certificate_instance_0253 : OAI.SidorenkoCounterexample.ProofCertificate_0253 := by
  constructor
  intro c0 c1 c2 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19
  exact @certificate_proof_0253 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19

include hω hS in
theorem certificate_proof_0254 (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha))^3 =
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha) L.val M.val N.val) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have h := uniform_preimage_card (avoidanceTripleReduction ω S ha hω hS A B C)
    (avoidanceTripleReduction_uniform ω S ha hω hS h2 A B C hA hB hC)
    (fun p => TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val p.1.val p.2.1.val p.2.2.val)
  change Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) * _ =
    Nat.card (LagTripleOrbit _ L M N) * _ at h
  rw [Nat.card_congr (lagTripleOrbitEquiv _ L M N)] at h
  simp only [Nat.card_prod] at h
  convert h using 1; ring

private instance certificate_instance_0254 : OAI.SidorenkoCounterexample.ProofCertificate_0254 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21
  exact @certificate_proof_0254 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21

end AvoidanceTripleCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem certificate_proof_0255 (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (z : ℕ) (hz : 2*z = finrank K (ReducedSpace ω S))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (AvoidanceSpace ω S A) : ℝ) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)) ≤
      (4^z * lagrangianConstant z^2) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  let Ω := symplecticReductionForm ω S ha
  have hΩ := symplecticReductionForm_alt ω S ha
  have hp := symplecticLagrangian_card_pos Ω hΩ
  have hb := symplectic_transverseTriple_probability_lower Ω hΩ
    (symplecticReductionForm_nondegenerate ω S ha hω) z hz L M N hLM hLN hMN
  have hi : (Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) : ℝ) *
      (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 =
      (Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
    exact_mod_cast avoidanceOrbitFiber_card_identity ω S ha hω hS
      (isUnit_of_invertible (2 : K)).ne_zero A B C hA hB hC L M N
  have hpos : 0 < (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 := by exact pow_pos (by exact_mod_cast hp) _
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    _ ≤ ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) *
      ((4^z * lagrangianConstant z^2) * Nat.card (OrderedTripleOrbit Ω L.val M.val N.val)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4^z * lagrangianConstant z^2) *
      ((Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)))) := by ring
    _ = _ := by rw [←hi]; ring

private instance certificate_instance_0255 : OAI.SidorenkoCounterexample.ProofCertificate_0255 := by
  constructor
  intro c0 c1 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26
  exact @certificate_proof_0255 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26

end AvoidanceTripleBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [FiniteDimensional K E] [Finite E]
end ConfigurationOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
variable [Finite E]
end PairOrbitAssembly
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationCount
section FixedPairCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
end FixedPairCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E] [Invertible (2:K)]
end PairMass
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0232 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0233 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0234 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0235 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0236 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0237 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0238 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0239 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0240 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0241 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0242 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0243 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0244 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0245 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0246 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0247 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0248 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0249 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0250 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0251 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0252 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0253 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0254 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0255 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

