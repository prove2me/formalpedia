-- Prove2me | solution 1 for MazurAdmissible.AdmissibleChain.nonempty_of_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ea460ff1-7600-5f75-9b44-b19071652c98

import Mathlib
import Definitions.Def_MazurAdmissible_GaloisModule
import Theorems.Thm_MazurAdmissible_AdmissibleChain_exists_map_addEquiv
import Theorems.Thm_MazurAdmissible_exists_admissibleChain_filtAlpha_eq_add
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup

set_option autoImplicit false

p2m_open "MazurAdmissible P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible"

namespace MazurAdmissible
p2m_export "MazurAdmissible" "OpenAction IsTrivialStep IsCyclotomicStep AdmissibleChain AdmissibleChain.exists_map_addEquiv exists_admissibleChain_filtAlpha_eq_add"
p2m_open "MazurAdmissible"

variable {M : Type*} [AddCommGroup M]

local notation "Qbar" => AlgebraicClosure ℚ

namespace OpenAction p2m_export "MazurAdmissible.OpenAction" "φ mk hker" end OpenAction
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private noncomputable def _root_.MazurAdmissible.OpenAction.restrict (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ K, Φ.φ σ x ∈ K) : OpenAction ↥K where
  φ :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨Φ.φ σ (x : M), hK σ (x : M) x.2⟩
          invFun := fun x => ⟨Φ.φ σ⁻¹ (x : M), hK σ⁻¹ (x : M) x.2⟩
          left_inv := fun x => by
            ext
            change (Φ.φ σ⁻¹) ((Φ.φ σ) (x : M)) = x
            rw [← AddAut.mul_apply', ← map_mul, inv_mul_cancel, map_one, AddAut.one_apply']
          right_inv := fun x => by
            ext
            change (Φ.φ σ) ((Φ.φ σ⁻¹) (x : M)) = x
            rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']
          map_add' := fun x y => by ext; exact map_add (Φ.φ σ) (x : M) (y : M) }
      map_one' := by
        ext x
        change Φ.φ 1 (x : M) = x
        rw [map_one]; rfl
      map_mul' := fun σ τ => by
        ext x
        change Φ.φ (σ * τ) (x : M) = Φ.φ σ (Φ.φ τ (x : M))
        rw [map_mul]; rfl }
  hker := by
    apply Subgroup.isOpen_mono _ Φ.hker
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext x
    change Φ.φ σ (x : M) = x
    rw [hσ]; rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.restrict"
p2m_open_scoped "MazurAdmissible.OpenAction" in
@[scoped simp] theorem OpenAction.restrict_coe (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ K, Φ.φ σ x ∈ K) (σ : Qbar ≃ₐ[ℚ] Qbar) (x : ↥K) :
    ((Φ.restrict K hK).φ σ x : M) = Φ.φ σ x := rfl

p2m_reactivate "P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible.OpenAction"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in
private theorem _root_.MazurAdmissible.OpenAction.map_eq_of_stable (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ K, Φ.φ σ x ∈ K) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    K.map (Φ.φ σ : M →+ M) = K := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact hK σ x hx
  · intro x hx
    refine ⟨Φ.φ σ⁻¹ x, hK σ⁻¹ x hx, ?_⟩
    change (Φ.φ σ) ((Φ.φ σ⁻¹) x) = x
    rw [← AddAut.mul_apply', ← map_mul, mul_inv_cancel, map_one, AddAut.one_apply']

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.map_eq_of_stable"
namespace OpenAction
p2m_open_scoped "MazurAdmissible.OpenAction" in

private noncomputable def _root_.MazurAdmissible.OpenAction.quotient (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ K, Φ.φ σ x ∈ K) : OpenAction (M ⧸ K) where
  φ :=
    { toFun := fun σ => QuotientAddGroup.congr K K (Φ.φ σ) (Φ.map_eq_of_stable K hK σ)
      map_one' := by
        ext x
        induction x using QuotientAddGroup.induction_on with
        | H x =>
          change (QuotientAddGroup.mk (Φ.φ 1 x) : M ⧸ K) = QuotientAddGroup.mk x
          rw [map_one]; rfl
      map_mul' := fun σ τ => by
        ext x
        induction x using QuotientAddGroup.induction_on with
        | H x =>
          change (QuotientAddGroup.mk (Φ.φ (σ * τ) x) : M ⧸ K) = QuotientAddGroup.mk (Φ.φ σ (Φ.φ τ x))
          rw [map_mul]; rfl }
  hker := by
    apply Subgroup.isOpen_mono _ Φ.hker
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change (QuotientAddGroup.mk (Φ.φ σ x) : M ⧸ K) = QuotientAddGroup.mk x
      rw [hσ]; rfl

end OpenAction
p2m_export "MazurAdmissible" "OpenAction.quotient"
p2m_open_scoped "MazurAdmissible.OpenAction" in
theorem OpenAction.quotient_mk (Φ : OpenAction M) (K : AddSubgroup M)
    (hK : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ K, Φ.φ σ x ∈ K) (σ : Qbar ≃ₐ[ℚ] Qbar) (x : M) :
    (Φ.quotient K hK).φ σ (QuotientAddGroup.mk x) = QuotientAddGroup.mk (Φ.φ σ x) := rfl

namespace AdmissibleChain p2m_export "MazurAdmissible.AdmissibleChain" "tag hmono step n mk hact htop hbot hcard exists_map_addEquiv" end AdmissibleChain
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

def AdmissibleChain.ofEqBot {p : ℕ} (Φ : OpenAction M) (h : (⊤ : AddSubgroup M) = ⊥) :
    AdmissibleChain p Φ where
  n := 0
  step := fun _ => ⊥
  hbot := rfl
  htop := h.symm
  hmono := fun i => i.elim0
  tag := fun i => i.elim0
  hcard := fun i => i.elim0
  hact := fun i => i.elim0

p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

def AdmissibleChain.ofCardEq {p : ℕ} (Φ : OpenAction M) (tag : Bool)
    (hcard : Nat.card M = p)
    (hact : if tag then IsTrivialStep Φ ⊥ ⊤ else IsCyclotomicStep p Φ ⊥ ⊤) :
    AdmissibleChain p Φ where
  n := 1
  step := fun i => if i = 0 then ⊥ else ⊤
  hbot := rfl
  htop := by simp
  hmono := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  tag := fun _ => tag
  hcard := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, if_true, if_neg one_ne_zero]
    rw [← hcard]

    rw [AddSubgroup.bot_addSubgroupOf]
    exact Nat.card_congr ((QuotientAddGroup.quotientBot).toEquiv.trans AddSubgroup.topEquiv.toEquiv)
  hact := fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simpa using hact

end MazurAdmissible
p2m_reactivate "P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible.OpenAction P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible"

namespace MazurAdmissible
p2m_export "MazurAdmissible" "OpenAction IsTrivialStep IsCyclotomicStep AdmissibleChain AdmissibleChain.exists_map_addEquiv exists_admissibleChain_filtAlpha_eq_add"
p2m_open "MazurAdmissible"

variable {M : Type*} [AddCommGroup M]

namespace AdmissibleChain
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

private theorem _root_.MazurAdmissible.AdmissibleChain.step_stable {p : ℕ} (hp : p.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain p Φ) (i : Fin (c.n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : M) (hx : x ∈ c.step i) : Φ.φ σ x ∈ c.step i := by

  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := by
    have hdeg : (Polynomial.cyclotomic p (AlgebraicClosure ℚ)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
  have hσζ : ∃ a : ℕ, σ ζ = ζ ^ a := by
    have hpow : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, _, ha⟩ := hζ.eq_pow_of_pow_eq_one hpow
    exact ⟨a, ha.symm⟩
  induction i using Fin.induction generalizing x with
  | zero =>
      rw [c.hbot, AddSubgroup.mem_bot] at hx
      rw [c.hbot, AddSubgroup.mem_bot, hx, map_zero]
  | succ i ih =>
      have hle := c.hmono i
      have hact := c.hact i
      rcases htag : c.tag i with _ | _
      · simp only [htag, Bool.false_eq_true, if_false] at hact
        obtain ⟨a, ha⟩ := hσζ
        have h1 : Φ.φ σ x - a • x ∈ c.step i.castSucc := hact σ ζ hζ a ha x hx
        have : Φ.φ σ x = (Φ.φ σ x - a • x) + a • x := (sub_add_cancel _ _).symm
        rw [this]
        exact (c.step i.succ).add_mem (hle h1) ((c.step i.succ).nsmul_mem hx a)
      · simp only [htag, if_true] at hact
        have h1 : Φ.φ σ x - x ∈ c.step i.castSucc := hact σ x hx
        have : Φ.φ σ x = (Φ.φ σ x - x) + x := (sub_add_cancel _ _).symm
        rw [this]; exact (c.step i.succ).add_mem (hle h1) hx

end AdmissibleChain
p2m_export "MazurAdmissible" "AdmissibleChain.step_stable"
p2m_open_scoped "MazurAdmissible.AdmissibleChain" in

theorem AdmissibleChain.nonempty_of_addSubgroup_impl
    {p : ℕ} (hp : p.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N)
    (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (c : AdmissibleChain p Φ) :
    Nonempty (AdmissibleChain p ΦN) := by
  classical
  have hK : ∀ (i : Fin (c.n + 1)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ∀ x ∈ N ⊓ c.step i, Φ.φ σ x ∈ N ⊓ c.step i :=
    fun i σ x hx => ⟨hN σ x hx.1, c.step_stable hp i σ x hx.2⟩
  have main : ∀ i : Fin (c.n + 1),
      Nonempty (AdmissibleChain p (Φ.restrict (N ⊓ c.step i) (hK i))) := by
    intro i
    induction i using Fin.induction with
    | zero =>
        refine ⟨AdmissibleChain.ofEqBot _ ?_⟩
        rw [eq_bot_iff]
        intro x _
        rw [AddSubgroup.mem_bot]
        ext
        rw [ZeroMemClass.coe_zero]
        exact AddSubgroup.mem_bot.mp (le_of_eq c.hbot x.2.2)
    | succ i ih =>
        obtain ⟨d⟩ := ih
        have hle : N ⊓ c.step i.castSucc ≤ N ⊓ c.step i.succ := inf_le_inf_left N (c.hmono i)

        let Φ' : OpenAction ↥(N ⊓ c.step i.succ) := Φ.restrict (N ⊓ c.step i.succ) (hK i.succ)
        let N₂ : AddSubgroup ↥(N ⊓ c.step i.succ) := (N ⊓ c.step i.castSucc).addSubgroupOf (N ⊓ c.step i.succ)
        have hN₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ N₂, Φ'.φ σ x ∈ N₂ := by
          intro σ x hx
          rw [AddSubgroup.mem_addSubgroupOf] at hx ⊢
          exact hK i.castSucc σ _ hx

        let e : ↥(N ⊓ c.step i.castSucc) ≃+ ↥N₂ := (AddSubgroup.addSubgroupOfEquivOfLe hle).symm
        obtain ⟨dN, -, -⟩ := AdmissibleChain.exists_map_addEquiv
          (Φ := Φ.restrict (N ⊓ c.step i.castSucc) (hK i.castSucc)) (Φ' := Φ'.restrict N₂ hN₂) e
          (fun σ x => by ext; rfl) d

        let g : ↥(N ⊓ c.step i.succ) →+ ↥(c.step i.succ) := AddSubgroup.inclusion inf_le_right
        have hg : N₂ ≤ ((c.step i.castSucc).addSubgroupOf (c.step i.succ)).comap g := by
          intro x hx
          rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
          rw [AddSubgroup.mem_addSubgroupOf] at hx
          exact hx.2
        let f := QuotientAddGroup.map N₂ ((c.step i.castSucc).addSubgroupOf (c.step i.succ)) g hg
        have hf : Function.Injective f := by
          rw [injective_iff_map_eq_zero]
          intro x hx
          induction x using QuotientAddGroup.induction_on with
          | H x =>
            rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
            rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
            exact ⟨x.2.1, hx⟩
        have hdvd : Nat.card (↥(N ⊓ c.step i.succ) ⧸ N₂) ∣ p :=
          (AddSubgroup.card_dvd_of_injective f hf).trans (dvd_of_eq (c.hcard i))
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
        ·
          have hKK : N ⊓ c.step i.castSucc = N ⊓ c.step i.succ := by
            refine le_antisymm hle ?_
            intro x hx
            haveI := (Nat.card_eq_one_iff_unique.mp h1).1
            have h0 : (QuotientAddGroup.mk ⟨x, hx⟩ : ↥(N ⊓ c.step i.succ) ⧸ N₂) = 0 := Subsingleton.elim _ _
            rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
            exact h0
          obtain ⟨d', -, -⟩ := AdmissibleChain.exists_map_addEquiv
            (Φ := Φ.restrict (N ⊓ c.step i.castSucc) (hK i.castSucc)) (Φ' := Φ')
            (AddEquiv.addSubgroupCongr hKK) (fun σ x => by ext; rfl) d
          exact ⟨d'⟩
        ·
          have hactQ : if c.tag i then IsTrivialStep (Φ'.quotient N₂ hN₂) ⊥ ⊤
              else IsCyclotomicStep p (Φ'.quotient N₂ hN₂) ⊥ ⊤ := by
            have hact := c.hact i
            rcases htag : c.tag i with _ | _
            · simp only [htag, Bool.false_eq_true, if_false] at hact ⊢
              intro σ ζ hζ a ha x _
              induction x using QuotientAddGroup.induction_on with
              | H y =>
                rw [AddSubgroup.mem_bot, OpenAction.quotient_mk, ← QuotientAddGroup.mk_nsmul,
                  ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
                refine ⟨N.sub_mem (hN σ _ y.2.1) (N.nsmul_mem y.2.1 a), ?_⟩
                exact hact σ ζ hζ a ha y.1 y.2.2
            · simp only [htag, if_true] at hact ⊢
              intro σ x _
              induction x using QuotientAddGroup.induction_on with
              | H y =>
                rw [AddSubgroup.mem_bot, OpenAction.quotient_mk,
                  ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
                refine ⟨N.sub_mem (hN σ _ y.2.1) y.2.1, ?_⟩
                exact hact σ y.1 y.2.2
          let dQ : AdmissibleChain p (Φ'.quotient N₂ hN₂) :=
            AdmissibleChain.ofCardEq (Φ'.quotient N₂ hN₂) (c.tag i) hp' hactQ
          obtain ⟨c', -, -⟩ := exists_admissibleChain_filtAlpha_eq_add hp Φ' N₂ hN₂
            (Φ'.restrict N₂ hN₂) (fun _ _ => rfl) (Φ'.quotient N₂ hN₂) (fun _ _ => rfl) dN dQ
          exact ⟨c'⟩
  obtain ⟨d⟩ := main (Fin.last c.n)
  have htop : N ⊓ c.step (Fin.last c.n) = N := by rw [c.htop, inf_top_eq]
  obtain ⟨d', -, -⟩ := AdmissibleChain.exists_map_addEquiv
    (Φ := Φ.restrict (N ⊓ c.step (Fin.last c.n)) (hK _)) (Φ' := ΦN)
    (AddEquiv.addSubgroupCongr htop) (fun σ x => by ext; rw [hΦN]; rfl) d
  exact ⟨d'⟩

end MazurAdmissible
p2m_reactivate "P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible.OpenAction P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible"

open _root_.MazurAdmissible _root_.P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup.MazurAdmissible in
theorem solution
    {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) (Φ : OpenAction M)
    (N : AddSubgroup M)
    (hN : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ N, Φ.φ σ x ∈ N)
    (ΦN : OpenAction ↥N)
    (hΦN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥N), (ΦN.φ σ x : M) = Φ.φ σ x)
    (c : AdmissibleChain p Φ) :
    Nonempty (AdmissibleChain p ΦN) :=
  AdmissibleChain.nonempty_of_addSubgroup_impl hp Φ N hN ΦN hΦN c

end S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup
end P2MW
export P2MW.S_MazurAdmissible_AdmissibleChain_nonempty_of_addSubgroup (solution)
