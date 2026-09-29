-- Prove2me | solution 1 for MvFormalGroup.CartierModule.nonempty_basis_span_frobenius_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/08f0e176-d39c-5e92-8220-cb1a178d1575

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_span_frobenius_of_finite_quotient
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcFrobImage

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
variable (Φ : MvFormalGroup d k) [Φ.IsComm]

theorem mem_span_p_of_coeff_zero [PerfectRing k p] (w : WittVector p k) (hw : w.coeff 0 = 0) :
    w ∈ Ideal.span {(p : WittVector p k)} := by
  by_cases h0 : w = 0
  · rw [h0]; exact Submodule.zero_mem _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  rcases m with - | m
  · rw [pow_zero, one_mul] at hw
    exact absurd hw hb
  · exact Ideal.mem_span_singleton.mpr ⟨(p : WittVector p k) ^ m * b, by ring⟩

theorem frobenius_frobeniusEquiv_symm [PerfectRing k p] (w : WittVector p k) :
    WittVector.frobenius ((WittVector.frobeniusEquiv p k).symm w) = w := by
  rw [← WittVector.frobeniusEquiv_apply]
  exact (WittVector.frobeniusEquiv p k).apply_symm_apply w

omit [CharP k p] in

theorem frobenius_mem_span_p [PerfectRing k p] {w : WittVector p k}
    (hw : w ∈ Ideal.span {(p : WittVector p k)}) :
    WittVector.frobenius w ∈ Ideal.span {(p : WittVector p k)} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hw
  rw [map_mul, map_natCast]
  exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩

omit [CharP k p] in

theorem isSMulRegular
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p)))) :
    IsSMulRegular (CartierModule p Φ) (p : WittVector p k) := by
  have hinj : Function.Injective (map (p := p) ((p : ℕ) : MvFormalGroup.End Φ)) := by
    refine map_injective_of_finite_quotient p Φ Φ _ ?_
    rw [MvFormalGroup.End.toPowerSeries_natCast]
    exact hfin
  intro f g hfg
  apply hinj
  have hdict : ∀ x : CartierModule p Φ,
      (p : WittVector p k) • x = map ((p : ℕ) : MvFormalGroup.End Φ) x := fun x => by
    rw [natCast_smul_eq_nsmul', ← endAct_natCast]
    rfl
  have h' : (p : WittVector p k) • f = (p : WittVector p k) • g := hfg
  rwa [hdict, hdict] at h'

theorem frobenius_injective
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p)))) :
    Function.Injective (frobenius (p := p) (Φ := Φ)) := by
  intro f g hfg
  apply isSMulRegular Φ hfin
  show (p : WittVector p k) • f = (p : WittVector p k) • g
  rw [← verschiebung_frobenius_eq_smul, ← verschiebung_frobenius_eq_smul, hfg]

omit [CharP k p] in

theorem mem_smul_top_iff (x : CartierModule p Φ) :
    x ∈ (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ)) ↔
      ∃ m : CartierModule p Φ, x = (p : WittVector p k) • m := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩; exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩; exact ⟨m, Submodule.mem_top, rfl⟩

theorem p_smul_eq_frobenius_verschiebung (m : CartierModule p Φ) :
    (p : WittVector p k) • m = frobenius (verschiebung m) := by
  rw [frobenius_verschiebung, verschiebung_frobenius_eq_smul]

omit [CharP k p] in

theorem tangent_sum_teichmuller_smul (γ : Fin d → CartierModule p Φ)
    (hγ : ∀ i, tangent (γ i) = Pi.single i 1) (a : Fin d → k) :
    tangent (∑ i, WittVector.teichmuller p (a i) • γ i) = a := by
  rw [map_sum]
  funext j
  rw [Finset.sum_apply]
  have hterm : ∀ i, tangent (WittVector.teichmuller p (a i) • γ i) j = a i * (Pi.single i (1 : k) : Fin d → k) j := by
    intro i
    rw [tangent_smul_witt, WittVector.teichmuller_coeff_zero, hγ i, Pi.smul_apply, smul_eq_mul]
  simp_rw [hterm]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.single_apply, if_neg (Ne.symm hij), mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem exists_eq_sum_add_verschiebung (γ : Fin d → CartierModule p Φ)
    (hγ : ∀ i, tangent (γ i) = Pi.single i 1) (f : CartierModule p Φ) :
    ∃ g : CartierModule p Φ,
      f = (∑ i, WittVector.teichmuller p (tangent f i) • γ i) + verschiebung g := by
  have h0 : tangent (f - ∑ i, WittVector.teichmuller p (tangent f i) • γ i) = 0 := by
    rw [map_sub, tangent_sum_teichmuller_smul Φ γ hγ, sub_self]
  obtain ⟨g, hg⟩ := (tangent_eq_zero_iff_exists_verschiebung_eq p Φ _).mp h0
  exact ⟨g, by rw [hg]; abel⟩

section Basis

variable [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in

theorem mk_sum (x : Fin d → CartierModule p Φ) :
    (Submodule.Quotient.mk (∑ i, x i) : CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) =
      ∑ i, (Submodule.Quotient.mk (x i) : CartierModule p Φ ⧸
        (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) :=
  map_sum (Submodule.mkQ (Ideal.span {(p : WittVector p k)} • ⊤ :
    Submodule (WittVector p k) (CartierModule p Φ))) x Finset.univ

omit [CharP k p] [PerfectRing k p] in

theorem mk_smul (w : WittVector p k) (m : CartierModule p Φ) :
    (Submodule.Quotient.mk (w • m) : CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) =
      Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) w •
        (Submodule.Quotient.mk m : CartierModule p Φ ⧸
          (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) :=
  (Module.Quotient.mk_smul_mk (CartierModule p Φ) (Ideal.span {(p : WittVector p k)}) w m).symm

noncomputable def frobClass (γ : Fin d → CartierModule p Φ) (i : Fin d) :
    CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ)) :=
  Submodule.Quotient.mk (frobenius (γ i))

omit [PerfectRing k p] in

theorem mk_frobenius_mem_span (γ : Fin d → CartierModule p Φ)
    (hγ : ∀ i, tangent (γ i) = Pi.single i 1) (f : CartierModule p Φ) :
    (Submodule.Quotient.mk (frobenius f) : CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) ∈
      Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
        (Set.range (frobClass (p := p) Φ γ)) := by
  obtain ⟨g, hg⟩ := exists_eq_sum_add_verschiebung Φ γ hγ f
  have hF : frobenius f = (∑ i, WittVector.frobenius (WittVector.teichmuller p (tangent f i)) •
      frobenius (γ i)) + (p : WittVector p k) • g := by
    conv_lhs => rw [hg]
    rw [map_add, map_sum, p_smul_eq_frobenius_verschiebung]
    simp only [frobenius_smul]
  rw [hF, Submodule.Quotient.mk_add, mk_sum]
  have hp0 : (Submodule.Quotient.mk ((p : WittVector p k) • g) : CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ((mem_smul_top_iff Φ _).mpr ⟨g, rfl⟩)
  rw [hp0, add_zero]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mk_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_frobClass
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p))))
    (γ : Fin d → CartierModule p Φ) (hγ : ∀ i, tangent (γ i) = Pi.single i 1) :
    LinearIndependent (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (frobClass (p := p) Φ γ) := by
  rw [Fintype.linearIndependent_iff]
  intro r hr i₀

  choose w hw using fun i => Ideal.Quotient.mk_surjective (r i)

  have hsum : (Submodule.Quotient.mk (∑ i, w i • frobenius (γ i)) : CartierModule p Φ ⧸
      (Ideal.span {(p : WittVector p k)} • ⊤ : Submodule (WittVector p k) (CartierModule p Φ))) = 0 := by
    rw [mk_sum, ← hr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mk_smul, hw i]
    rfl
  obtain ⟨m, hm⟩ := (mem_smul_top_iff Φ _).mp ((Submodule.Quotient.mk_eq_zero _).mp hsum)

  set w' : Fin d → WittVector p k := fun i => (WittVector.frobeniusEquiv p k).symm (w i) with hw'
  have hlhs : (∑ i, w i • frobenius (γ i)) = frobenius (∑ i, w' i • γ i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [frobenius_smul, hw', frobenius_frobeniusEquiv_symm]
  rw [hlhs, p_smul_eq_frobenius_verschiebung] at hm
  have hVM : (∑ i, w' i • γ i) = verschiebung m := frobenius_injective Φ hfin hm

  have htan : (fun i => (w' i).coeff 0) = 0 := by
    have h1 : tangent (∑ i, w' i • γ i) = fun j => (w' j).coeff 0 := by
      rw [map_sum]
      funext j
      rw [Finset.sum_apply]
      have hterm : ∀ i, tangent (w' i • γ i) j = (w' i).coeff 0 * (Pi.single i (1 : k) : Fin d → k) j := by
        intro i
        rw [tangent_smul_witt, hγ i, Pi.smul_apply, smul_eq_mul]
      simp_rw [hterm]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        rw [Pi.single_apply, if_neg (Ne.symm hij), mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [← h1, hVM, tangent_verschiebung]
  have h0 : (w' i₀).coeff 0 = 0 := congrFun htan i₀

  have hmem : w i₀ ∈ Ideal.span {(p : WittVector p k)} := by
    have := frobenius_mem_span_p (mem_span_p_of_coeff_zero (w' i₀) h0)
    rwa [hw', frobenius_frobeniusEquiv_symm] at this
  rw [← hw i₀]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

end Basis

end P2mKcFrobImage

open P2mKcFrobImage MvFormalGroup MvFormalGroup.CartierModule in
theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Φ : MvFormalGroup d k) [Φ.IsComm]
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range (Φ.nthSeries p)))) :
    Nonempty (Module.Basis (Fin d) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
        (Set.range fun f : MvFormalGroup.CartierModule p Φ =>
          (Submodule.Quotient.mk (MvFormalGroup.CartierModule.frobenius f) :
            MvFormalGroup.CartierModule p Φ ⧸
              (Ideal.span {(p : WittVector p k)} • ⊤ :
                Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))))) := by

  choose γ hγ using fun i : Fin d => tangent_surjective p Φ (Pi.single i 1)

  let b := Module.Basis.span (linearIndependent_frobClass Φ hfin γ hγ)

  have heq : Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      (Set.range (frobClass (p := p) Φ γ)) =
      Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
        (Set.range fun f : CartierModule p Φ =>
          (Submodule.Quotient.mk (frobenius f) : CartierModule p Φ ⧸
            (Ideal.span {(p : WittVector p k)} • ⊤ :
              Submodule (WittVector p k) (CartierModule p Φ)))) := by
    apply le_antisymm
    · refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨γ i, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact mk_frobenius_mem_span Φ γ hγ f
  exact ⟨b.map (LinearEquiv.ofEq _ _ heq)⟩

end S_MvFormalGroup_CartierModule_nonempty_basis_span_frobenius_of_finite_quotient
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_span_frobenius_of_finite_quotient (solution)
